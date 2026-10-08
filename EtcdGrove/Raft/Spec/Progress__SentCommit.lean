/- Port of election_proof/spec_Progress__SentCommit.v (feb5c73d4). -/
import EtcdGrove.Raft.InvRaftPhys

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

/-- `pr.SentCommit(commit)` is one field assignment (`tracker.Progress.SentCommit.impl`,
`EtcdRaft/Code/go_etcd_io/raft/v3/tracker.lean`): `pr.sentCommit = commit` --
`progressSentCommit p commit` (`Defs.lean`). The field is read by
`Progress.CanBumpCommit`. -/
abbrev tracker.Progress.SentCommit.spec : Prop :=
  ∀ (pr : Loc) (p : Progress) (commit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hpr" ∷ ownProgress pr p }}
    (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"SentCommit"))
      (Val #commit))
  {{ RET #(); ownProgress pr (progressSentCommit p commit) }}

end spec

end EtcdGrove
end Perennial
