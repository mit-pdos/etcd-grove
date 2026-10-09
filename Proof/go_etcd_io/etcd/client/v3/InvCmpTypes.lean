/-
`TypeRepr` instances (named and underlying types) for the `clientv3` and protobuf types the
comparison builders and the client's own methods touch, straight from their `TypeAssumptions`
(as `InvStore.lean` does for the protobuf messages, `InvNew.lean` for `Client`): without them,
the `StructFieldRef` and `GoAlloc` steps find `TypeRepr` through the structs' `IntoValTyped`
instances, built from the `sorry` instances ("axiomatized type") of their names-only fields
(`Client.cfg`, ...), putting them in the trust base for nothing. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClient

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

instance (priority := high) cmpTypes_client_typeRepr :
    TypeRepr go_etcd_io.etcd.client.v3.Client.ty go_etcd_io.etcd.client.v3.Client :=
  go.type_repr_underlying (u := go_etcd_io.etcd.client.v3.Client.underlying)

instance (priority := high) cmpTypes_client_typeRepr_u :
    TypeRepr go_etcd_io.etcd.client.v3.Client.underlying go_etcd_io.etcd.client.v3.Client :=
  go.type_repr_underlying (u := go_etcd_io.etcd.client.v3.Client.underlying)

instance (priority := high) cmpTypes_compare_typeRepr :
    TypeRepr etcdserverpb.Compare.ty etcdserverpb.Compare :=
  go.type_repr_underlying (u := etcdserverpb.Compare.underlying)

instance (priority := high) cmpTypes_compare_typeRepr_u :
    TypeRepr etcdserverpb.Compare.underlying etcdserverpb.Compare :=
  go.type_repr_underlying (u := etcdserverpb.Compare.underlying)

end defs

end EtcdGrove
end Perennial
