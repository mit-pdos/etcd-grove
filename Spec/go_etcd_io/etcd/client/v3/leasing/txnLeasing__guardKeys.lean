/-
`txn.guardKeys(ops)` (`client/v3/leasing/txn.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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

/-- **`txn.guardKeys(ops)`**: for each key a non-get operation writes (once), the comparison
"its lease key was created at or before this client's entry revision" (`Rev`): comparisons, in a
slice whose spare capacity is owned. -/
abbrev txnLeasing.guardKeys.spec : Prop :=
  ∀ (txn lkv : Loc) (γ : LeasingNames) (pfx : GoString) (dq : DFrac) (sl : GoSlice)
    (os : List OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ structFieldRef txnLeasing go!"lkv" txn ↦{dq} lkv ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ opsAt sl os }}
    (App (Val (txn @!! go.GoType.PointerType txnLeasing.ty @!! go!"guardKeys")) (Val #sl))
  {{ (cmps : GoSlice), RET #cmps; structFieldRef txnLeasing go!"lkv" txn ↦{dq} lkv ∗ lkvReader lkv γ pfx ∗
      ∃ ms : List CmpModel, cmpsAt cmps ms ∗
        ownSliceCap go_etcd_io.etcd.client.v3.Cmp cmps (DFrac.own 1) }}

end spec

end leasing
end EtcdGrove
end Perennial
