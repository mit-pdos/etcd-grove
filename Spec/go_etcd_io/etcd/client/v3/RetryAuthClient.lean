/-
`clientv3.RetryAuthClient(c)` (`client/v3/retry.go`, translated for the auth plan's E2h).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvAuthConn

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

/-- `RetryAuthClient(c)` on a `*Client` whose connection is `conn` (read-only): a new
`*retryAuthClient` over a stub on `conn` (`retryAuthAt`), as an `AuthClient`. -/
abbrev RetryAuthClient.spec : Prop :=
  ∀ (cl conn : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"conn" cl ↦□ conn }}
    (App (Val (@! go_etcd_io.etcd.client.v3.RetryAuthClient)) (Val #cl))
  {{ (v : GoInterface), RET #v; ∃ rac : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryAuthClient.ty) #rac⌝ ∗
      retryAuthAt rac conn }}

end spec

end EtcdGrove
end Perennial
