/-
`lkv.leaseID()` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lkv.leaseID()`** (read lock), once a session was set: the current session's lease, not
`NoLease`. -/
abbrev leasingKV.leaseID.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ sessionReady γ }}
    (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"leaseID")) (Val #()))
  {{ (id : w64), RET #id; lkvReader lkv γ pfx ∗ ⌜id ≠ W64 0⌝ }}

end spec

end leasing
end EtcdGrove
end Perennial
