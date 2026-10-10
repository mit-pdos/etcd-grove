/-
`lkv.monitorLease(ctx, key, rev)` (`client/v3/leasing/kv.go`; unit 5: specified here, proved with the monitors). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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

/-- **`lkv.monitorLease(ctx, key, rev)`** (a goroutine of `get`, with the reader slot it was
given): it returns. -/
abbrev leasingKV.monitorLease.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (key : GoString) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ context.isContext ctx cs }}
    (App (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"monitorLease")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #rev))
  {{ RET #(); True }}

end spec

end leasing
end EtcdGrove
end Perennial
