/-
`clientv3.RetryKVClient(c)` (`client/v3/retry.go`, translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `RetryKVClient(c)` on a `*Client` whose connection is `conn` (read-only): a new
`*retryKVClient` over a stub on `conn` (`retryKVAt`), as a `KVClient`. -/
abbrev RetryKVClient.spec : Prop :=
  ∀ (cl conn : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"conn" cl ↦□ conn }}
    (App (Val (@! go_etcd_io.etcd.client.v3.RetryKVClient)) (Val #cl))
  {{ (v : GoInterface), RET #v; ∃ rkv : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty) #rkv⌝ ∗
      retryKVAt rkv conn }}

end spec

end EtcdGrove
end Perennial
