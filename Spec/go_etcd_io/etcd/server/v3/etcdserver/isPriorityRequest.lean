/-
`isPriorityRequest(r)` (`util.go`): a lease revocation. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `isPriorityRequest(r)` on a request (all but its header read-only): whether it revokes a
lease. -/
abbrev isPriorityRequest.spec : Prop :=
  ∀ (p : Loc) (rq : apply.IRRModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ irrNoHdrIs p rq }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.isPriorityRequest)) (Val #p))
  {{ RET #rq.leaseRevoke.isSome; True }}

end spec

end EtcdGrove
end Perennial
