/-
`lkv.monitorSession()` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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

/-- **`lkv.monitorSession()`** (`NewKV`'s goroutine, with the session monitor's resources): until
`lkv.ctx` is done, makes a fresh entries map (the cache's entries frozen, a step of the cache's
log), creates a session (`concurrency.NewSession`), sets it and closes `sessionc` under the cache's
lock, and waits for the session to end. It returns. -/
abbrev leasingKV.monitorSession.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ sessionMonitor lkv γ }}
    (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"monitorSession")) (Val #()))
  {{ RET #(); True }}

end spec

end leasing
end EtcdGrove
end Perennial
