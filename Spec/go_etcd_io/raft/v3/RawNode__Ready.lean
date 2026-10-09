/-
Port of `election_proof/spec_RawNode__Ready.v` (857d09190).

Lean notes: As for `raft.Step.spec`, the section fixes `hlc := HasLC.hasLC` and has
`[AllG GF]` (the spec mentions ghost state). `ready_rnstate`, `ready_nstate` are
`readyRnstate`, `readyNstate`; Rocq's `pending.self <$> selfs` is
`selfs.map Pending.self`; `zero_val _` is written at its type.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode
public import Proof.go_etcd_io.raft.v3.StepLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- The `RawNode` state after `Ready`: the previous soft state is the node's, the
previous hard state the node's unless that is empty (`acceptReady` only records a
non-empty `Ready.HardState`), and the local messages to step on `Advance` are the
self-addressed responses from `msgsAfterAppend`, an acknowledgement of the log up to its
last entry if there were unstable entries, and an acknowledgement of the committed
entries handed out, if any. -/
def readyRnstate [FfiSyntax] (s : NState) (rs : RNState) (selfs : List (Option Msg))
    (ce : List raftpb.Entry) : RNState :=
  ⟨nodeSoftstate s,
   (if hsEmptyAbs (nodeHardstate s) then rs.hard else nodeHardstate s),
   selfs.map Pending.self ++
   (if s.logst.uents = [] then []
    else [Pending.appendAck s.term (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))]) ++
   (if ce = [] then [] else [Pending.applyAck ce])⟩

/-- The node after `Ready`: the outbox handed to the application, the unstable entries
in progress and the handed-out ones the application's to persist (`logAcceptUnstable`),
`applying` at the last committed entry handed out (`logAcceptApplying`; `sz` is
`entsSize` of them). -/
def readyNstate [FfiSyntax] (s : NState) (ce : List raftpb.Entry) (sz : w64) : NState :=
  { s with outbox := [],
           logst := logAcceptApplying (logAcceptUnstable s.logst) ce sz }

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- `rn.Ready()` (`rawnode.go:133`) is `readyWithoutAccept` then `acceptReady`; both
are stepped through inline in the proof, with the raft struct open
(`ownRaftPhys_view`): `readyWithoutAccept` appends `msgsAfterAppend`'s outgoing
messages to `rd.Messages = r.msgs` in place, into `r.msgs`' spare capacity, and the
struct is a consistent `ownRaftPhys` again only once `acceptReady` has set both queues
to `nil` -- in between a `send` would overwrite `rd.Messages`. So neither half has a
spec of its own (notes/raft-replication-model.md, "Phase 4").

Premises: `Advance` ran since the last `Ready` (`acceptReady` `Panicf`s on a non-empty
`stepsOnAdvance`); the previous `Ready`'s entries were appended to the storage
(`ownRawNode_persist`); no snapshot is pending (handing one out and `appliedSnap` are
phase 2).

The `Ready` it returns:
- `Entries`: the unstable entries not handed out before, read-only;
- `CommittedEntries`: a prefix of the committed entries after `applying` (empty while
  applying is paused), read-only; the slice's capacity stays with the node
  (`pendingOwn`), since the `MsgStorageApplyResp` `Advance` steps carries this slice and
  `Step`'s spec asks to own its capacity; and globally committed: the global committed
  log (`isCommitted`, `Protocol`) has `ce` right after its first `applying` entries --
  the entries the application applies are the cluster's, at their indices (from
  `ownRaftGhost_committed`);
- `Messages`: the outbox, the application's slice now; each message is what
  `ownRaftPhys` recorded (`msgAbs`) and its abstraction was in the outbox, so
  `isMessage`;
- `HardState`/`SoftState`/`MustSync` as the body computes them, `Snapshot` empty,
  `ReadStates` nil.
Ghost: the outbox is dropped (`step_drain`). -/
abbrev RawNode.Ready.spec : Prop :=
  ∀ (cfg : GSet w64) (γ : RaftNames) (rn : Loc) (id : w64)
    (s : NState) (ps : PState) (rs : RNState),
  γ.reCfg = cfg →
  NStateRel s ps →
  rs.steps = [] →
  s.logst.unpersisted = [] →
  s.logst.snap = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hrn" ∷ ownRawNode cfg rn id s rs ∗
      "Hghost" ∷ ownRaftGhost γ id ps }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Ready")) (Val #()))
  {{ (rd : Ready) (ce : List raftpb.Entry) (sz : w64)
      (ms : List raftpb.Message) (selfs : List (Option Msg)), RET #rd;
      "Hrn" ∷ ownRawNode cfg rn id (readyNstate s ce sz) (readyRnstate s rs selfs ce) ∗
      "Hghost" ∷ ownRaftGhost γ id { ps with outbox := [] } ∗
      "%Hrel" ∷ ⌜NStateRel (readyNstate s ce sz) { ps with outbox := [] } ∧
                 Step cfg id ps [] { ps with outbox := [] }⌝ ∗
      "#Hents" ∷ rd.Entries' ↦*□ nextUnstable s.logst ∗
      "#Hce" ∷ rd.CommittedEntries' ↦*□ ce ∗
      "%Hcepre" ∷ ⌜ce <+: logCommittedEnts s.logst⌝ ∗
      "#Hcommitted" ∷ (∃ pre, isCommitted γ (pre ++ ce) ∗
                       ⌜pre.length = (uint.Z s.logst.applying).toNat⌝) ∗
      "Hmsgs" ∷ rd.Messages' ↦* ms ∗
      "Hmsgs_cap" ∷ ownSliceCap raftpb.Message rd.Messages' (DFrac.own 1) ∗
      "#Hmsgs_abs" ∷ ([∗list] m ∈ ms, ∃ a, msgAbs m a ∗
                        ⌜∀ x, a = some x → x ∈ ps.outbox⌝) ∗
      "#Hselfs" ∷ ⌜∀ x, some x ∈ selfs → x ∈ ps.outbox⌝ ∗
      "#Hout" ∷ ([∗list] x ∈ ps.outbox, isMessage γ x) ∗
      "%Hhard" ∷ ⌜rd.HardState' =
                  (if nodeHardstate s = rs.hard then zero_val raftpb.HardState
                   else hardstateVal (nodeHardstate s))⌝ ∗
      "Hsoft" ∷ (if nodeSoftstate s = rs.soft
                 then iprop(⌜rd.SoftState' = null⌝)
                 else rd.SoftState' ↦□ softstateVal (nodeSoftstate s)) ∗
      "%Hsync" ∷ ⌜rd.MustSync' =
                  decide (nextUnstable s.logst ≠ [] ∨
                          s.vote ≠ rs.hard.vote ∨
                          s.term ≠ rs.hard.term)⌝ ∗
      "%Hsnapz" ∷ ⌜rd.Snapshot' = zero_val raftpb.Snapshot ∧
                   rd.ReadStates' = slice.nil⌝ }}

end spec

end EtcdGrove
end Perennial
