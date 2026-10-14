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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lkv.monitorLease(ctx, key, rev)`** (a goroutine of `get`, started after an acquisition at
revision `rev`, once a session was set, with the reader slot it was given): it returns (it watches
the lease key and rescinds the lease when another client puts `"REVOKE"` into it). -/
abbrev leasingKV.monitorLease.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (key : GoString) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ sessionReady γ ∗ context.isContext ctx cs ∗
      ⌜0 ≤ sint.Z rev ∧ sint.Z rev < 2 ^ 63 - 1⌝ }}
    (App (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"monitorLease")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #rev))
  {{ RET #(); True }}

end spec

end leasing
end EtcdGrove
end Perennial
