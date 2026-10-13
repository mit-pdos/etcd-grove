/-
Port of election_proof/spec_ProgressTracker__ConfState.v (feb5c73d4).

Lean notes: the type of Rocq's untyped binder `tv` is written out
(`tracker.ProgressTracker`), as `ownTracker` forces it.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `p.ConfState()` is the `ConfState` of the active configuration: the voters (some
permutation of `cfg`; really sorted), the learners (the tracked ids outside `cfg`; since
2026-10-13, reconfiguration stage L -- until then empty), and -- since `ownTracker` is a
simple configuration -- empty `VotersOutgoing` and `LearnersNext`. For those two the
length is all any caller needs. -/
abbrev tracker.ProgressTracker.ConfState.spec : Prop :=
  ∀ (cfg : GSet w64) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTracker cfg tv t }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"ConfState"))
      (Val #()))
  {{ (cs : raftpb.ConfState) (xs ls : List w64), RET #cs;
      trk ↦ tv ∗ ownTracker cfg tv t ∗
      cs.Voters' ↦* xs ∗ cs.Learners' ↦* ls ∗
      ⌜xs ≡ₚ elements cfg ∧ ls ≡ₚ elements (domSet t.prs \ cfg) ∧
        cs.VotersOutgoing'.len = W64 0 ∧
        cs.LearnersNext'.len = W64 0 ∧
        cs.AutoLeave' = false⌝ }}

end spec

end EtcdGrove
end Perennial
