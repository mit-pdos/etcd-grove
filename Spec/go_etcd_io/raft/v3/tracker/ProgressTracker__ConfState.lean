/-
Port of election_proof/spec_ProgressTracker__ConfState.v (feb5c73d4).

Lean notes: the type of Rocq's untyped binder `tv` is written out
(`tracker.ProgressTracker`), as `ownTracker` forces it.
-/
module

public import Proof.go_etcd_io.raft.v3.InvTrackerC
public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `p.ConfState()` is the `ConfState` of the active configuration (tracker.go:
`Voters: p.Voters[0].Slice()`, `VotersOutgoing: p.Voters[1].Slice()`, `Learners:
quorum.MajorityConfig(p.Learners).Slice()`, `LearnersNext: ...`, `AutoLeave: p.AutoLeave`):
each list a permutation of its set (really sorted).

Raft v3.7 (`notes/raft-retarget-plan.md`): the result is a `*pb.ConfState`, a fresh
`&pb.ConfState{...}` whose `AutoLeave` is a fresh `new(p.AutoLeave)`; since stage R1 the caller
gets it as an owned conf state (`csPts`, `InvPb.lean`: the four lists, the `AutoLeave` cell, set,
the hidden fields' invariant; stage R0 gave the struct, the cell and the slices apart). Until the
retarget the result was the `ConfState` value, with `cs.AutoLeave' = c.autoLeave`.

At any configuration since 2026-10-13 (reconfiguration stage A1; `ownTrackerC`): the four sets
of `c` and its `AutoLeave`. The statement at a simple configuration (`ownTracker cfg`: the
voters `cfg`, the learners the tracked ids outside `cfg`, and -- for the empty outgoing
voters and staged learners -- only the lengths, all any caller needs) was
`tracker.ProgressTracker.ConfState.spec_simple`; it had no caller and is gone (2026-10-17). -/
abbrev tracker.ProgressTracker.ConfState.spec : Prop :=
  ∀ (c : CfgM) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTrackerC c tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"ConfState"))
      (Val #()))
  {{ (csl : Loc) (xs os ls lns : List w64), RET #csl;
      trk ↦ tv ∗ ownTrackerC c tv t ∗
      csPts csl (DFrac.own 1) (ConfStateM.mk xs ls os lns c.autoLeave) true ∗
      ⌜xs ≡ₚ elements c.incoming ∧ os ≡ₚ elements c.outgoing ∧ ls ≡ₚ elements c.learners ∧
        lns ≡ₚ elements c.learnersNext⌝ }}

end spec

end EtcdGrove
end Perennial
