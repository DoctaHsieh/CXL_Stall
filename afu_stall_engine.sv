// =================================================================
// afu_stall_engine.sv
//
// Per-channel AXI read-address stall engine for the CXL Type 3
// example design.
//
// Every AR beat is accepted whenever there is room; requests matching
// an armed target are diverted into a small queue instead of being
// forwarded, and non-matching requests pass straight through. Queued
// entries are replayed downstream once their timer expires.
//
// arready is deasserted only when
//   * the MC is not accepting,
//   * a replay is using the AR port this cycle, or
//   * the incoming request shares an ARID with a held entry (below).
// It is NEVER deasserted because the queue is full. A target that
// arrives while every slot is busy is forwarded unstalled instead
// ("bypass", reported in status bit 33). Holding arready low for a
// full queue was the one condition that correlated with host resets
// on hardware: with 2 targets per channel and constant traffic both
// channels sat full for long stretches and the host went down, while
// the same traffic with the queue never full ran clean.
//
// So with FIFO_DEPTH = 2, any two target reads per channel are held
// at once, and unrelated reads always flow.
//
// ORDERING
//   AXI4 allows reads with different ARIDs to complete out of order,
//   but reads sharing an ARID must complete in issue order. Replaying
//   a held request after later requests have gone downstream is
//   therefore legal only if none of those later requests share its
//   ARID.
//
//   The previous revision forwarded a same-ID request PAST the held
//   one ("pass it through instead of stalling it"), which is exactly
//   the illegal reorder. That path was unreachable at FIFO_DEPTH = 1
//   (a full queue already dropped arready) but becomes live at 2+.
//   This revision backpressures instead: while an entry with ID x is
//   held, any incoming request with ID x -- target or not -- waits at
//   arready until the held entry has been replayed. Consequences:
//     * at most one held entry per ARID, so release order among held
//       entries can never reorder within an ID;
//     * a same-ID wait is bounded by the held entry's stall timer,
//       itself bounded by TIMEOUT_CYCLES.
//   conflict_cycles counts cycles spent in that wait, so software can
//   see when it happens.
//
// SAFETY
//   CXL.mem reads are CPU loads. A core issuing one is blocked until
//   data returns; holding it past the CXL completion timeout produces
//   a machine check, not an error code. Every entry therefore carries
//   an age counter that force-releases at TIMEOUT_CYCLES regardless
//   of its stall timer and regardless of software state. Do not
//   remove it, and keep TIMEOUT_CYCLES well under 1 ms.
//
//   Clearing stall_en zeroes every timer, so all held entries replay
//   within a few cycles. Nothing is ever dropped.
// =================================================================

package afu_stall_pkg;
  // Armed addresses (shared by both channels). Past ~8 the comparators
  // get expensive; switch to a BRAM bitmap indexed by
  // (araddr - window_base) >> 7 at that point.
  localparam int STALL_NUM_TARGETS = 4;

  // Concurrent stalls per channel. Fixed at synthesis; software may
  // use anywhere from 0 to this many without a rebuild. Reported to
  // software in status bits [39:36].
  localparam int STALL_FIFO_DEPTH  = 2;

  // Hard release deadline in afu_clk cycles. ~100 us at 500 MHz.
  localparam int STALL_TIMEOUT     = 50000;

  // Compare above the cache-line offset. araddr always arrives 64B
  // aligned, so bits [5:0] carry no information.
  localparam int STALL_ADDR_LSB    = 6;
endpackage


module afu_stall_engine
  import afu_stall_pkg::*;
#(
  parameter int NUM_TARGETS    = STALL_NUM_TARGETS,
  parameter int FIFO_DEPTH     = STALL_FIFO_DEPTH,
  parameter int TIMEOUT_CYCLES = STALL_TIMEOUT,
  parameter int ADDR_LSB       = STALL_ADDR_LSB
)(
  input  logic                              clk,
  input  logic                              rstn,

  // upstream: from the CXL IP
  input  mc_axi_if_pkg::t_to_mc_axi4        up_to_mc,
  output mc_axi_if_pkg::t_from_mc_axi4      up_from_mc,

  // downstream: to mc_top
  output mc_axi_if_pkg::t_to_mc_axi4        dn_to_mc,
  input  mc_axi_if_pkg::t_from_mc_axi4      dn_from_mc,

  // control, already synchronised to clk
  input  logic [NUM_TARGETS-1:0][63:0]      stall_addr,
  input  logic [NUM_TARGETS-1:0]            stall_target_en,
  input  logic                              stall_en,
  input  logic [15:0]                       stall_cycles,

  // status (counters saturate, they never wrap)
  output logic [7:0]                        occupancy,
  output logic [7:0]                        max_occupancy,
  output logic [15:0]                       stall_events,
  output logic                              fifo_full_sticky,
  output logic                              bypass_sticky,
  output logic [7:0]                        arid_seen,
  output logic [15:0]                       conflict_cycles
);

  localparam int IDX_W = (FIFO_DEPTH <= 1) ? 1 : $clog2(FIFO_DEPTH);

  // ---------------------------------------------------------------
  // queue state
  // ---------------------------------------------------------------
  mc_axi_if_pkg::t_to_mc_axi4 ent_req   [FIFO_DEPTH];
  logic [FIFO_DEPTH-1:0]      ent_valid;
  logic [15:0]                ent_timer [FIFO_DEPTH];
  logic [31:0]                ent_age   [FIFO_DEPTH];
  logic [FIFO_DEPTH-1:0]      ent_eligible;

  logic              alloc_valid, fifo_full;
  logic [IDX_W-1:0]  alloc_idx;

  // registered release selection (see the release block below)
  logic              rel_busy;
  logic [IDX_W-1:0]  rel_sel;
  logic              release_active;
  logic [IDX_W-1:0]  rel_idx;

  // ---------------------------------------------------------------
  // target match
  // ---------------------------------------------------------------
  logic                   match;
  logic [NUM_TARGETS-1:0] target_hit;

  always_comb begin
    for (int t = 0; t < NUM_TARGETS; t++)
      target_hit[t] = stall_target_en[t] &&
                      ((64'(up_to_mc.araddr) >> ADDR_LSB) ==
                       (stall_addr[t]        >> ADDR_LSB));
    match = stall_en && (|target_hit);
  end

  // ---------------------------------------------------------------
  // same-ID hazard
  //
  // True when the incoming request's ARID matches any held entry,
  // including one that is mid-replay (still valid until its
  // handshake). Such a request is NOT accepted -- see ORDERING above.
  // ---------------------------------------------------------------
  logic arid_conflict;

  always_comb begin
    arid_conflict = 1'b0;
    for (int i = 0; i < FIFO_DEPTH; i++)
      if (ent_valid[i] && (ent_req[i].arid == up_to_mc.arid))
        arid_conflict = 1'b1;
  end

  // An entry may leave when its stall timer expires, or
  // unconditionally once it has aged out.
  always_comb
    for (int i = 0; i < FIFO_DEPTH; i++)
      ent_eligible[i] = ent_valid[i] &&
                        ((ent_timer[i] == 16'd0) ||
                         (ent_age[i]   >= 32'(TIMEOUT_CYCLES)));

  // lowest free slot
  always_comb begin
    alloc_valid = 1'b0;
    alloc_idx   = '0;
    for (int i = FIFO_DEPTH-1; i >= 0; i--)
      if (!ent_valid[i]) begin
        alloc_valid = 1'b1;
        alloc_idx   = IDX_W'(i);
      end
  end

  // Candidate for release: lowest eligible slot. This is only a
  // CANDIDATE -- it must not be used directly to drive the AR channel.
  //
  // AXI4 requires every AR payload field to stay stable from ARVALID
  // until ARREADY. A combinational priority encoder does not satisfy
  // that: if a lower-numbered slot becomes eligible while we are still
  // waiting for ARREADY on a higher one, the selection moves and the
  // address changes underneath an asserted ARVALID. That is a protocol
  // violation and it can wedge the memory controller.
  //
  // So the selection is registered below and held until the handshake
  // completes. Because at most one held entry exists per ARID, the
  // choice between eligible entries never affects same-ID order.
  logic             rel_cand_valid;
  logic [IDX_W-1:0] rel_cand_idx;

  always_comb begin
    rel_cand_valid = 1'b0;
    rel_cand_idx   = '0;
    for (int i = FIFO_DEPTH-1; i >= 0; i--)
      if (ent_eligible[i]) begin
        rel_cand_valid = 1'b1;
        rel_cand_idx   = IDX_W'(i);
      end
  end

  // Registered, stable release selection.
  always_ff @(posedge clk or negedge rstn) begin
    if (!rstn) begin
      rel_busy <= 1'b0;
      rel_sel  <= '0;
    end
    else if (rel_busy) begin
      if (dn_from_mc.arready)          // handshake complete
        rel_busy <= 1'b0;
    end
    else if (rel_cand_valid) begin
      rel_busy <= 1'b1;
      rel_sel  <= rel_cand_idx;
    end
  end

  assign release_active = rel_busy;
  assign rel_idx        = rel_sel;

  assign fifo_full = ~alloc_valid;

  // ---------------------------------------------------------------
  // AR handshake
  //
  // Neither 'match' nor queue occupancy is in ar_ready. Whether a beat
  // is a target, and whether there is room to hold it, only decide
  // WHERE an accepted beat goes, never WHETHER it is accepted:
  //   target and a free slot   -> held
  //   target and queue full    -> forwarded now (bypass)
  //   not a target             -> forwarded now
  //
  // arid_conflict IS in ar_ready: a same-ID request must wait behind
  // the held one, target or not (AXI4 same-ID order). A bypassed
  // target therefore never overtakes a held entry with its own ID.
  // ---------------------------------------------------------------
  logic ar_ready, ar_accept, ar_divert, ar_forward, ar_bypass;

  assign ar_ready   = dn_from_mc.arready && !release_active && !arid_conflict;
  assign ar_accept  = up_to_mc.arvalid && ar_ready;
  assign ar_divert  = ar_accept &&  match &&  alloc_valid;
  assign ar_bypass  = ar_accept &&  match && !alloc_valid;
  assign ar_forward = ar_accept && !ar_divert;

  // ---------------------------------------------------------------
  // datapath
  //
  // Everything but the AR channel passes through untouched, so write
  // traffic keeps flowing while a read is being replayed.
  // ---------------------------------------------------------------
  always_comb begin
    dn_to_mc = up_to_mc;
    if (release_active) begin
      dn_to_mc.arvalid  = 1'b1;
      dn_to_mc.arid     = ent_req[rel_idx].arid;
      dn_to_mc.araddr   = ent_req[rel_idx].araddr;
      dn_to_mc.arlen    = ent_req[rel_idx].arlen;
      dn_to_mc.arsize   = ent_req[rel_idx].arsize;
      dn_to_mc.arburst  = ent_req[rel_idx].arburst;
      dn_to_mc.arprot   = ent_req[rel_idx].arprot;
      dn_to_mc.arqos    = ent_req[rel_idx].arqos;
      dn_to_mc.arcache  = ent_req[rel_idx].arcache;
      dn_to_mc.arlock   = ent_req[rel_idx].arlock;
      dn_to_mc.arregion = ent_req[rel_idx].arregion;
      dn_to_mc.aruser   = ent_req[rel_idx].aruser;
    end
    else begin
      dn_to_mc.arvalid = ar_forward;
    end
  end

  always_comb begin
    up_from_mc         = dn_from_mc;   // R channel straight through
    up_from_mc.arready = ar_ready;
  end

  // ---------------------------------------------------------------
  // sequential
  // ---------------------------------------------------------------
  logic [7:0] occ_next;
  always_comb occ_next = 8'($countones(ent_valid));

  logic conflict_wait;
  assign conflict_wait = up_to_mc.arvalid && arid_conflict;

  always_ff @(posedge clk or negedge rstn) begin
    if (!rstn) begin
      ent_valid        <= '0;
      occupancy        <= '0;
      max_occupancy    <= '0;
      stall_events     <= '0;
      fifo_full_sticky <= 1'b0;
      bypass_sticky    <= 1'b0;
      arid_seen        <= '0;
      conflict_cycles  <= '0;
      for (int i = 0; i < FIFO_DEPTH; i++) begin
        ent_timer[i] <= '0;
        ent_age[i]   <= '0;
      end
    end
    else if (!stall_en) begin
      // Disarming clears the counters and stops new diversions. Held
      // entries are released by the normal path first, because
      // ent_timer was zeroed, so nothing is dropped. arid_seen is kept
      // so the survey survives a disarm.
      occupancy        <= occ_next;
      max_occupancy    <= '0;
      stall_events     <= '0;
      fifo_full_sticky <= 1'b0;
      bypass_sticky    <= 1'b0;
      conflict_cycles  <= '0;
      for (int i = 0; i < FIFO_DEPTH; i++)
        ent_timer[i] <= '0;
      if (release_active && dn_from_mc.arready) begin
        ent_valid[rel_idx] <= 1'b0;
        ent_age[rel_idx]   <= '0;
      end
    end
    else begin
      // age and count down held entries
      for (int i = 0; i < FIFO_DEPTH; i++) begin
        if (ent_valid[i]) begin
          if (ent_timer[i] != 16'd0)
            ent_timer[i] <= ent_timer[i] - 16'd1;
          if (ent_age[i] != 32'hFFFF_FFFF)
            ent_age[i] <= ent_age[i] + 32'd1;
        end
      end

      // replay: retire the entry once the MC takes it
      if (release_active && dn_from_mc.arready) begin
        ent_valid[rel_idx] <= 1'b0;
        ent_timer[rel_idx] <= '0;
        ent_age[rel_idx]   <= '0;
      end

      // divert (never the same slot as a release: ar_ready is low
      // whenever release_active is high; alloc_idx is a free slot
      // because ar_divert requires alloc_valid)
      if (ar_divert) begin
        ent_req[alloc_idx]   <= up_to_mc;
        ent_valid[alloc_idx] <= 1'b1;
        ent_timer[alloc_idx] <= stall_cycles;
        ent_age[alloc_idx]   <= '0;
        if (stall_events != 16'hFFFF)
          stall_events <= stall_events + 16'd1;
      end

      if (conflict_wait && conflict_cycles != 16'hFFFF)
        conflict_cycles <= conflict_cycles + 16'd1;

      // which ARIDs the IP actually uses
      if (ar_accept)
        arid_seen <= arid_seen | 8'(up_to_mc.arid);

      if (fifo_full)
        fifo_full_sticky <= 1'b1;

      if (ar_bypass)
        bypass_sticky <= 1'b1;

      occupancy <= occ_next;
      if (occ_next > max_occupancy)
        max_occupancy <= occ_next;
    end
  end

endmodule