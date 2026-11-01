/- `RawNode.readyWithoutAccept`, Lean-first (2026-10-10): the first half of the proof of
`RawNode.Ready` (`RawNode__Ready.lean` until then, itself the port of
election_proof/proof_RawNode__Ready.v at 857d09190, finished in Lean), up to the call of
`acceptReady`, closed into `ownRawNodeReady`. The facts the application gets with the
`Ready` -- the committed entries extending `delivered`, the messages' `isRaftMsg` -- were
proved at the end of `Ready`'s proof; they come here, since `node.go` hands the `Ready` out
before accepting it.

Since 2026-10-10 the messages are appended with `wp_slice_append_undo`, so that the
loop keeps a way back to `r.msgs`' slice (`Hundo`, for `ownRawNodeReady_abandon`), and
their terms are bounded by the outbox's `OutTermOk` (2026-10-17: within the term ceiling; until
then, with pre-vote off, by the node's term).

Since 2026-10-13 the `ReadState`s are handed out (`rd.ReadStates = r.readStates` when not
empty): the slice read-only, and each one's `readStateRaw`, copied out of the ghost state
(`ownRaftGhost_readStates`; `InvRawnodeReady.lean`'s header).

Lean notes: `readyWithoutAccept`'s `rd` is tracked as `readyVal` (one field per argument).

Raft v3.7 (2026-10-16, stage R5, `notes/decisions.md` D8): the messages are pointers and are
**handed out** (`readyDq`: a response at half, its other half kept); `r.msgsAfterAppend`'s
messages are read through `GetTo` (each one's ownership looked up in the queue's
`[∗list]`); `r.hardState()` allocates a fresh read-only hard state (inlined, as
`raft.hardState`'s proof builds it), handed out in `rd.HardState` unless equal to
`prevHardSt`; `rd.Snapshot` stays `nil`; the read states are `readStatesPts`.
-/
module

public import Proof.go_etcd_io.raft.v3.LemmasReadyR
public import Spec.go_etcd_io.raft.v3.RawNode__readyWithoutAccept
public import Spec.go_etcd_io.raft.v3.raftLog__nextUnstableEnts
public import Spec.go_etcd_io.raft.v3.raftLog__nextCommittedEnts
public import Spec.go_etcd_io.raft.v3.SoftState__equal
public import Spec.go_etcd_io.raft.v3.isHardStateEqual
public import Spec.go_etcd_io.raft.v3.raftLog__hasNextUnstableSnapshot
public import Spec.go_etcd_io.raft.v3.raftLog__nextUnstableSnapshot
public import Spec.go_etcd_io.raft.v3.MustSync
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

set_option linter.unusedSectionVars false

section helpers
variable [GooseExts]

/-- The `Ready` `readyWithoutAccept` builds, field by field (D22 S-d3a: `Snapshot` `sn`, `nil`
unless a snapshot is pending and not in progress). -/
abbrev readyVal (sp hp : Loc) (rs ents : GoSlice) (sn : Loc) (ce msgs : GoSlice) (ms : Bool) : Ready :=
  Ready.mk sp hp rs ents sn ce msgs ms

end helpers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The `Ready`'s `SoftState`, made read-only (Rocq's inline `iAssert`). -/
private theorem soft_persist (c : Prop) [Decidable c] (sp : Loc) (v : SoftState) :
    ⊢ (if c then iprop(⌜sp = null⌝) else sp ↦ v) -∗
      |==> (if c then iprop(⌜sp = null⌝ : IProp GF) else sp ↦□ v) := by
  by_cases h : c
  · rw [ite_pos' h, ite_pos' h]
    iintro H; imodintro; iexact H
  · rw [ite_neg' h, ite_neg' h]
    iintro H
    ipersist H
    imodintro
    iexact H

/-- ... then forgotten down to what `acceptReady` needs: `nil`, or some read-only
`SoftState`. -/
private theorem soft_or (c : Prop) [Decidable c] (sp : Loc) (v : SoftState) :
    ⊢ (if c then iprop(⌜sp = null⌝ : IProp GF) else sp ↦□ v) -∗
      (⌜sp = null⌝ ∨ ∃ v' : SoftState, sp ↦□ v') := by
  by_cases h : c
  · rw [ite_pos' h]
    iintro H; ileft; iexact H
  · rw [ite_neg' h]
    iintro #H
    iright
    iexists v
    iexact H

theorem hsOpt_of_hsRO (p : Loc) (h : HardStateM) : hsRO (GF := GF) p h ⊢ hsOpt p h := by
  iintro H; unfold hsOpt; iright; iexact H

theorem RawNode.readyWithoutAccept.wp_proof
    (wp_raftLog_nextUnstableEnts : raftLog.nextUnstableEnts.spec (GF := GF) (hG := hG))
    (wp_raftLog_nextCommittedEnts : raftLog.nextCommittedEnts.spec (GF := GF) (hG := hG))
    (wp_SoftState_equal : SoftState.equal.spec (GF := GF) (hG := hG))
    (wp_isHardStateEqual : isHardStateEqual.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextUnstableSnapshot :
      raftLog.hasNextUnstableSnapshot.spec (GF := GF) (hG := hG))
    (wp_raftLog_nextUnstableSnapshot :
      raftLog.nextUnstableSnapshot.spec (GF := GF) (hG := hG))
    (wp_MustSync : MustSync.spec (GF := GF) (hG := hG))
    (wp_Message_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hlc := HasLC.hasLC)) :
    RawNode.readyWithoutAccept.spec (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

end proof

end EtcdGrove
end Perennial
