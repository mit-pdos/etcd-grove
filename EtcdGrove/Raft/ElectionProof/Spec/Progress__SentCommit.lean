/-
Port of `election_proof/spec_Progress__SentCommit.v`.
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

/-- `pr.SentCommit(commit)` is one field assignment (`tracker.Progress.SentCommit.impl`,
`Perennial/Code/go_etcd_io/raft/v3/tracker.lean`): `pr.sentCommit = commit`. The field
is read only by `Progress.CanBumpCommit`, which nothing on the election path calls. -/
abbrev tracker.Progress.SentCommit.spec : Prop :=
  ∀ (pr : Loc) (pv : tracker.Progress) (iv : tracker.Inflights) (commit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hpr" ∷ ownProgress pr pv iv }}
    (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"SentCommit"))
      (Val #commit))
  {{ RET #(); ownProgress pr { pv with sentCommit' := commit } iv }}

end spec

end EtcdGrove
end Perennial
