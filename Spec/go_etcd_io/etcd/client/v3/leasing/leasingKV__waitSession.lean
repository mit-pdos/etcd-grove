/-
`lkv.waitSession(ctx)` (`client/v3/leasing/kv.go`; unit 5: specified here, proved with the monitors). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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

/-- **`lkv.waitSession(ctx)`**: waits for the `sessionc` it read under the read lock to be closed
(`nil`: a session was set and the entries map made, `sessionReadyQ`), or for `lkv.ctx` or `ctx` to
be done (an error). -/
abbrev leasingKV.waitSession.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ context.isContext ctx cs }}
    (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"waitSession")) (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; lkvReader lkv γ pfx ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ sessionReadyQ γ)) }}

end spec

end leasing
end EtcdGrove
end Perennial
