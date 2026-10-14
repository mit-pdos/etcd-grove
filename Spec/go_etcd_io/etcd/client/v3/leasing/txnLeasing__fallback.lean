/-
`txn.fallback(ops)` (`client/v3/leasing/txn.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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

/-- **`txn.fallback(ops)`**: for each operation that is not a get, a get of its lease keys
(`OpGet(pfx ++ key, WithRange(pfx ++ end))`): gets a transaction can run. -/
abbrev txnLeasing.fallback.spec : Prop :=
  ∀ (txn lkv : Loc) (γ : LeasingNames) (pfx : GoString) (dq : DFrac) (sl : GoSlice)
    (os : List OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ structFieldRef txnLeasing go!"lkv" txn ↦{dq} lkv ∗ isLeasingKV lkv γ pfx ∗ opsAt sl os }}
    (App (Val (txn @!! go.GoType.PointerType txnLeasing.ty @!! go!"fallback")) (Val #sl))
  {{ (fb : GoSlice), RET #fb; structFieldRef txnLeasing go!"lkv" txn ↦{dq} lkv ∗
      ∃ fos : List OpFull, opsAt fb fos ∗ ⌜∀ o ∈ fos, txnOpOf o = some (.get o)⌝ }}

end spec

end leasing
end EtcdGrove
end Perennial
