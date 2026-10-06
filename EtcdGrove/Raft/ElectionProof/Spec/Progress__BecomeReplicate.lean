/-
Port of `election_proof/spec_Progress__BecomeReplicate.v`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

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

/-- `pr.BecomeReplicate()` moves a `Progress` into the replicating state. It says
nothing about votes, terms or roles, so the model does not see it. -/
abbrev tracker.Progress.BecomeReplicate.spec : Prop :=
  ∀ (pr : Loc) (pv : tracker.Progress) (iv : tracker.Inflights),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownProgress pr pv iv }}
    (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"BecomeReplicate"))
      (Val #()))
  {{ RET #(); ∃ pv' iv', ownProgress pr pv' iv' }}

end spec

end EtcdGrove
end Perennial
