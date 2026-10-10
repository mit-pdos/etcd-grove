/-
`lkv.Compact(ctx, rev, opts...)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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

/-- **`lkv.Compact(ctx, rev, opts...)`** is the client's `Compact`: whatever `lkv.kv.Compact`
(the client's `KV`) does (returning, as a Go method of its signature does, a pair: the leasing
KV's `return lkv.kv.Compact(...)` takes it apart and rebuilds it). -/
abbrev leasingKV.Compact.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterface) (rev : w64) (sl : GoSlice)
    (Φ : val → IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx -∗
    (∀ kv : GoInterfaceOk, structFieldRef leasingKV go!"kv" lkv ↦□ GoInterface.ok kv -∗
      WP (App (App (App (Val #(methods kv.ty go!"Compact" kv.v)) (Val #ctx)) (Val #rev)) (Val #sl))
        {{ v, ∃ (resp : Loc) (err : GoInterface), ⌜v = PairV #resp #err⌝ ∗ Φ v }}) -∗
    WP (App (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"Compact")) (Val #ctx))
      (Val #rev)) (Val #sl)) {{ Φ }}

end spec

end leasing
end EtcdGrove
end Perennial
