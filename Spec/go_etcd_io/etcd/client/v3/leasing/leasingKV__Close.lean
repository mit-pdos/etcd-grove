/-
`lkv.Close()` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lkv.Close()`**: cancels `lkv.ctx` and waits for the wait group (the session monitor,
`clearOldRevokes` and the lease monitors), with the whole "open" token (no `get` running). It
returns. -/
abbrev leasingKV.Close.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ isLeasingCancel lkv ∗ leasingOpen γ 1 }}
    (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"Close")) (Val #()))
  {{ RET #(); True }}

end spec

end leasing
end EtcdGrove
end Perennial
