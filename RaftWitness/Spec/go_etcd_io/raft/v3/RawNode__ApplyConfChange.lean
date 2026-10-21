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

**Any change, detached (2026-10-13, reconfiguration stage A2).** The premise is now `CCApplies`:
for every learner set the node may track, the change is carried out (`ccApplyM` answers: no
`confchange` error, no undefined transition, `issues/raft-unknown-transition-panic.md`), leaves
the node a voter of either half (a removed or demoted leader would step down only with
`Config.StepDownOnRemoval`, which the node's client-facing state does not record; a removed
candidate would stay one) and tracks at most `2^62` ids. A shrinking change (`CCShrink`, the
scope above, which implies `CCApplies` at a voter) keeps `ownRawNode γ` as before. Any other
change -- adding a learner, changing the voters, entering or leaving a joint configuration --
returns `ownRawNodeC c'.cfg rn id s'` (`InvRawnodeC.lean`): the node's memory at the new
configuration, with no ghost state and no `γ` -- the protocol is proved at a fixed voter set
only, and nothing says `γ.reCfg` is the new voters -- with the `ConfState` of `c'` (all four
lists, `AutoLeave`) and what `applyConfChange` did (`ApplyCCOkC`).

**The order of `ApplyConfChange` and `Advance`**, again: for a configuration-changing entry an
application must call `ApplyConfChange` *before* the `Advance` of the `Ready` that handed the
entry out. It is not a premise: neither `ownRawNode` nor `ownRawNodeC` records which
conf-change entries the configuration in use reflects (it would need the decoded entries'
history), so no predicate here can state it; the guarantee lost without it is the protocol's
(two entries committed at one index; and, by the same route, a removed candidate that goes on
to win would panic in `becomeLeader` on its missing `Progress`), which the detached predicate
does not claim anyway.

**raft v3.7 (2026-10-16, stage R5).** `ApplyConfChange(cc)` is `return
rn.raft.applyConfChange(cc.AsV2())`: the `*pb.ConfState` `applyConfChange` returns (stage R4),
fresh and owned (`csPts csp 1 cs true`), the record `cs : ConfStateM`; the facts on its lists are
those on the slices' contents before (the voters `xs`, learners `ls`, outgoing `os`, next
learners `lns`, now `cs`'s fields; "empty" was `len = 0`, now `= []`). `cc` is given back. -/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRawnode
public import RaftWitness.Proof.go_etcd_io.raft.v3.InvApplyConf
public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRawnodeC
-- `ApplyCCOkC`
public import RaftWitness.Spec.go_etcd_io.raft.v3.raft__applyConfChange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

-- (2026-10-16, stage R5) `DynCCPreOp` and `DynCCPre` moved to `InvRawnode.lean`.

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
    (dq : DFrac)
    -- (2026-10-14, stage B7 part 2) the dynamic mode's: the conf entry applied (at position `k`),
    -- and the configuration it gives
    (k : Nat) (e : EntryM) (cs' : CCState),
  -- the static mode (the voters fixed): the change applies at a voter
  (rs.mode = .static → CCApplies γ.reCfg id (ccV2Of o).1 (ccV2Of o).2) →
  -- (2026-10-20, witness support) and of a cluster without a witness: the static mode's change has
  -- no witness yet (NoWitReconf, `notes/raft-witness.md`)
  (rs.mode = .static → γ.reWit = W64 0 ∧ NoAddWit (ccV2Of o).2) →
  -- the dynamic mode: it is the next committed conf entry's decoded change, and applies
  (∀ dec c0 h0 h1, rs.mode = .dyn dec c0 h0 h1 → DynCCPre dec rs o k e cs') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "Hc" ∷ ownCCI c dq (some o) }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"ApplyConfChange")) (Val #c))
  {{ (csp : Loc) (cs : ConfStateM), RET #csp;
      "Hc" ∷ ownCCI c dq (some o) ∗
      -- (2026-10-16, stage R5) the fresh `*pb.ConfState` `applyConfChange` returns, owned, its
      -- `AutoLeave` cell set (until then `csp ↦ cs` with the voters' and learners' slices)
      "Hcs" ∷ csPts csp (DFrac.own 1) cs true ∗
      "Hres" ∷ (
        (⌜rs.mode = .static⌝ ∗ (
        -- a shrinking change: the node stays where it was
        (⌜CCShrink γ.reCfg (ccV2Of o).1 (ccV2Of o).2⌝ ∗
          ownRawNode γ rn id rs ∗
          ⌜cs.Voters' ≡ₚ elements γ.reCfg ∧ (∀ k ∈ cs.Learners', k ∉ γ.reCfg) ∧
            cs.VotersOutgoing' = [] ∧ cs.LearnersNext' = [] ∧
            cs.AutoLeave' = false⌝) ∨
        -- any other: detached, at the new configuration
        (⌜¬ CCShrink γ.reCfg (ccV2Of o).1 (ccV2Of o).2⌝ ∗
          ∃ (lrn : GSet w64) (c' : CCState) (s s' : NState),
            ownRawNodeC c'.cfg rn id s' ∗
            ⌜(∀ k ∈ lrn, k ∉ γ.reCfg) ∧
              ccApplyM (ccV2Of o).1 (ccV2Of o).2 (cfgState γ.reCfg lrn) = some c' ∧
              cs.Voters' ≡ₚ elements c'.cfg.incoming ∧
              cs.VotersOutgoing' ≡ₚ elements c'.cfg.outgoing ∧
              cs.Learners' ≡ₚ elements c'.cfg.learners ∧
              cs.LearnersNext' ≡ₚ elements c'.cfg.learnersNext ∧
              cs.AutoLeave' = c'.cfg.autoLeave ∧ ApplyCCOkC c'.cfg id s s'⌝))) ∨
        -- (2026-10-14, stage B7 part 2) the dynamic mode: the node at the new configuration,
        -- the entry applied (`StepR.applyConf`; a removed leader has stepped down)
        (⌜rs.mode.isDyn = true⌝ ∗
          ownRawNode γ rn id { rs with cfg := cs', capplied := k + 1 } ∗
          ⌜cs.Voters' ≡ₚ elements cs'.cfg.incoming ∧
            cs.VotersOutgoing' ≡ₚ elements cs'.cfg.outgoing ∧
            cs.Learners' ≡ₚ elements cs'.cfg.learners ∧
            cs.LearnersNext' ≡ₚ elements cs'.cfg.learnersNext ∧
            cs.AutoLeave' = cs'.cfg.autoLeave⌝)) }}

end spec

end EtcdGrove
end Perennial
