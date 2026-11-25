-- The copy for the part `KvNet/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/RawNode__acceptReady.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`RawNode.acceptReady` (`rawnode.go:405`), Lean-first (2026-10-10): the second half of
`RawNode.Ready`, which `node.go`'s `run` calls after handing the `Ready` to the application.

Lean notes: as `RawNode.Ready.spec` (`hlc := HasLC.hasLC`, `[AllG GF]`).
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import KvNet.Proof.go_etcd_io.raft.v3.TraceFits
public import KvNet.Proof.go_etcd_io.raft.v3.RawNodeAt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `rn.acceptReady(rd)`, for the `Ready` `readyWithoutAccept` returned, with nothing in
between (`ownRawNodeReady`): the node's new state as after `RawNode.Ready` -- `delivered`
grows by `ce`, `unpersisted` is `es`, the local messages for `Advance` are queued
(`steps`, opaque); the lower bounds `outlb` and `unst` are reset (2026-10-10: nothing
is queued, and every unstable entry is handed out). The right to append `es` to the
node's storage is handed out before the call, since 2026-10-10 (`ownRawNodeReady_handout`:
the node comes in at `ownRawNodeReady … true`), and so are (2026-10-13) the messages' read
credits, with the drain of the abstract outbox. It sets `r.readStates` to `nil` (2026-10-13; the
`ReadState`s and their facts were handed out by `readyWithoutAccept`), a model step
(`Step.takeReads`) the node's state hides. `acceptReady` does not read `rd.Messages`,
which the application may already hold (`ms`, what `readyWithoutAccept` handed out there, is only an index of
`ownRawNodeReady`, since 2026-10-10). (2026-10-16, stage R5, D8: it does read the messages to
others of `msgsAfterAppend`' `To`, which it keeps at half (`ownRaftPhysReady`'s `Hother`); it
stores `rd.HardState` in `prevHardSt` when not empty; the queued acknowledgements are fresh
messages (`newStorageAppendRespMsg`, `newStorageApplyRespMsg`), the apply acknowledgement's
`Entries` the committed entries' slice.) (D22l, 2026-10-20: `prevHardSt`'s record moves to
`phsNext rs.phs h`, `h` the `Ready`'s hard state, `hsOpt rd.HardState' h`, which the caller
names.) (D22 S-d3a, 2026-10-21) With a snapshot (`L`): the acknowledgement queued shares the
`Ready`'s snapshot, the snapshot is in progress, and the node records the loan (`RNState.slent`);
either way no snapshot is restored since this `Ready` (`psnap` off). (2026-11-01, durability stage
I fix G2) The node records the batch's durable state (`readyDurable`, as the driver does:
`NodeDriverState.afterReady`) and the role after the `Ready`'s soft state `ss` (`roleAfter`).
(2026-11-11, trace-check Q8 stage 1 slice 28n) One spec for both modes: at a traced cluster the
`Ready` line (`traceReady`) moves the node's capability from the cut state to the accepted one
(`rnTrace_fireReady`) and hands out one token per handed-out message (`readyTok`, `True` untraced).
(#33 S4, 2026-11-24) **At the node's protocol state** (`RawNode.Ready.absSpec`'s second half): the node
comes in at the named state `s` (`ownRawNodeReadyS`) with the scope at `sc`, and leaves as
`ownRawNodeAt` at `s`'s protocol reading with the outbox and the read states cleared, its queue `qs'`,
its in-progress boundary `ip'`, the scope kept; in the scope, the queue reads as the outbox's
self-addressed messages, the hard state after the `Ready` is the node's, the durable state the
batch makes has the node's log, the entries handed out are the log's from the in-progress
boundary on, the boundary moves to the log's end, and no snapshot was handed out. -/
abbrev RawNode.acceptReady.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rd : Ready)
    (ce es : List EntryM) (ms : List QMsg) (h : HardStateM) (L : Option SnapLoan) (s : NState)
    (sc : Bool),
  -- (2026-11-11, trace-check Q8 stage 1 slice 28n; from 2026-11-09, Q8 stage 0, until then the
  -- premise `γ.reTrace = none`) one spec for both modes: at a traced cluster the `Ready` line's
  -- numbers within the trace's bound (the term below the ceiling, the log by the receipts' fit;
  -- (2026-11-12) named, `traceReadyFits`, until then `receiptBound GF + γ.reBoot.length ≤
  -- traceNumBound` spelled out)
  (γ.reTrace ≠ none → uint.Z rs.tc + 1 < traceNumBound ∧ traceReadyFits GF γ) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNodeReadyS γ rn id rs rd ce es ms true L s ∗
      "Hsc" ∷ rnScopeAt γ id (basicScope sc) rs s ∗
      "#Hh" ∷ hsOpt rd.HardState' h }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"acceptReady")) (Val #rd))
  {{ (steps : List Pending) (ss : Option (w64 × StateType)) (qs' : List Msg) (ip' : Nat), RET #();
      -- (2026-11-01, durability stage I fix G2) the `Ready`'s soft state, which the node records
      "#Hss" ∷ softStateIs rd.SoftState' ss ∗
      -- (2026-11-01, durability stage II (k)) `none` at a `nil` pointer
      "%Hssn" ∷ ⌜rd.SoftState' = null → ss = none⌝ ∗
      -- (#33 S4; until then `ownRawNode`) at `s`'s protocol reading, the outbox and the read states
      -- cleared
      -- (antithesis parity B1) over `RState`: `s`'s reading at some ghost prefix `fp`, the outbox and
      -- the read states cleared
      "Hrn" ∷ (∃ fp : List EntryM, ownRawNodeAt γ rn id
        { rs with delivered := rs.delivered ++ ce, unpersisted := es, steps := steps,
                  outlb := 0, unst := false, phs := phsNext rs.phs h, psnap := false,
                  slent := L, dur := readyDurable rs.dur (phsNext rs.phs h) L es,
                  role := roleAfter rs.role ss }
        { toRState rs fp s with
            p := { toPState s with outbox := [], rd := { (toPState s).rd with states := [] } } }
        qs' ip' (basicScope sc)) ∗
      -- (2026-11-11, slice 28n) the handed-out messages' tokens (`readyTok`: nothing untraced; the
      -- `Ready` line's `recvTokOf` traced, `trCap_fire_ready`)
      "Htoks" ∷ ([∗list] q ∈ ms, readyTok γ q.st) ∗
      -- (#33 S4) in the scope, the `Ready` against `s`
      "%Hout" ∷ ⌜sc = true →
        qs' ≡ₚ s.outbox.filter (fun m => decide (m.dst = id)) ∧
        phsNext rs.phs h = HardStateM.mk s.term s.vote s.logst.committed ∧
        (readyDurable rs.dur (phsNext rs.phs h) L es).ents = (toPState s).log ∧
        (∀ e0 ∈ es.head?, (toPState s).log.drop (uint.nat e0.Index' - 1) = es ∧
          uint.nat e0.Index' = uint.nat s.logst.inprogress) ∧
        ip' = (toPState s).log.length ∧ L = none⌝ }}

end spec

end EtcdGrove
end Perennial
