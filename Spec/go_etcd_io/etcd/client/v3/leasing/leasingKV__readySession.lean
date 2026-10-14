/-
`lkv.readySession()` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lkv.readySession()`** (read lock): `true` only if a session was set (and was not done when
it looked). -/
abbrev leasingKV.readySession.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx }}
    (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"readySession")) (Val #()))
  {{ (b : Bool), RET #b; lkvReader lkv γ pfx ∗ (if b then sessionReady γ else iprop(True)) }}

end spec

end leasing
end EtcdGrove
end Perennial
