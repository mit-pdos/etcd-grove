/-
`getRequestType(r)` (`v3_server.go`): the request's metric label. Lean-first (no Rocq
counterpart).
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

/-- `getRequestType(r)`: `reqTypeName rq` (`InvProposer.lean`), the first set field in the
switch's order. -/
abbrev getRequestType.spec : Prop :=
  ∀ (p : Loc) (rq : apply.IRRModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ irrNoHdrIs p rq }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.getRequestType)) (Val #p))
  {{ RET #(reqTypeName rq); True }}

end spec

end EtcdGrove
end Perennial
