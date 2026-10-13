/- `RawNode.ApplyConfChange` (rawnode.go), Lean-first (2026-10-13, reconfiguration stage D).

`ApplyConfChange(cc)` is `cs := rn.raft.applyConfChange(cc.AsV2()); return &cs`.

**Scope: a change that keeps the voters and only drops learners** (`CCShrink`, since
2026-10-13, reconfiguration stage L; until then `CCNoop`, an unchanged configuration). The
premise is the model's: `ccApplyM` of what `AsV2` makes of the change (`ccV2Of`), on the node's
configuration (`cfgState γ.reCfg lrn`, whatever its learners `lrn`), answers the same voters
and some of the learners -- e.g. a `ConfChange` with `NodeId = 0` (`ccApplyM_v1_noop`), which
`Changer.apply` skips, an `UpdateNode`, or a `RemoveNode` of a learner
(`ccShrink_removeLearner`). Adding a learner is specified one level down
(`raft.applyConfChange`, `ccVoterKeep_addLearner`) but not here: it needs the bound on the
tracked ids, which this layer cannot state without the learner set in `RNState`. Changing the
voters or joint consensus is not specified: the voter set the ghost state is about (`γ.reCfg`)
is fixed. The `RawNode`'s client-facing state is unchanged; inside, the node installs new
`Progress` objects and, at a leader, commits what the (same) quorums allow and sends appends:
one ghost step (`Step.reMatch`, `Step.commit`, `Step.sendApps`; `applyCCOk_step`).

**The order of `ApplyConfChange` and `Advance`** (`issues/raft-advance-before-applyconfchange.md`):
etcd-raft's guards against a second pending conf change (`hasUnappliedConfChanges` at a
campaign, `pendingConfIndex > applied` at the leader) read the *applied index*, which
`Advance` moves, while the configuration in use changes only here. An application must
therefore apply the conf-change entries of a `Ready`'s `CommittedEntries` with
`ApplyConfChange` **before** it calls `Advance` for that `Ready`; the documentation
(doc.go, step 4; node.go's `Advance`) allows the opposite, and the issue file shows two
committed entries at one index when a configuration-changing entry is applied after
`Advance`. **For the changes this spec covers the order does not matter for its
guarantees** -- the voters in use are the same before and after (a learner change cannot
affect a quorum), so a misled guard cannot break the ghost state -- so the spec takes no
premise about it (nor could it state one: `ownRawNode` does not record which
entries the application has applied). The spec of a configuration-changing
`ApplyConfChange` will have to.

Returned: a fresh `*ConfState` holding the voters (`cfg`'s, in some order) and the learners
(none of them a voter).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode
public import Proof.go_etcd_io.raft.v3.InvApplyConf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev RawNode.ApplyConfChange.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (c : GoInterface) (o : CCMsg)
    (dq : DFrac),
  CCShrink γ.reCfg (ccV2Of o).1 (ccV2Of o).2 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "Hc" ∷ ownCCI c dq (some o) }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"ApplyConfChange")) (Val #c))
  {{ (csp : Loc) (cs : raftpb.ConfState) (xs ls : List w64), RET #csp;
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "Hc" ∷ ownCCI c dq (some o) ∗
      "Hcs" ∷ csp ↦ cs ∗
      "Hvoters" ∷ cs.Voters' ↦* xs ∗
      "Hlearners" ∷ cs.Learners' ↦* ls ∗
      "%Hxs" ∷ ⌜xs ≡ₚ elements γ.reCfg⌝ ∗
      "%Hls" ∷ ⌜∀ k ∈ ls, k ∉ γ.reCfg⌝ ∗
      "%Hcs0" ∷ ⌜cs.VotersOutgoing'.len = W64 0 ∧
        cs.LearnersNext'.len = W64 0 ∧
        cs.AutoLeave' = false⌝ }}

end spec

end EtcdGrove
end Perennial
