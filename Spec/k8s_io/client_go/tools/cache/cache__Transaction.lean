/-
`(*cache).Transaction(txns...)` (`store.go:220`): each write keyed by the key function, then the
thread-safe store's `Transaction` (the batch path's store write). Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md` (fourth round).

The transformer is not applied (unlike `Add`/`Update`); the informers' store has none (`isCache`).
-/
module

public import Proof.k8s_io.client_go.tools.cache.BatchDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section model
variable [FfiSyntax]

/-- The write keyed by the key function `KF` (the key `cache.Transaction` computes). -/
def Tx.keyed (KF : GoInterface → GoString) (x : Tx) : Tx := { x with k := KF x.o }

@[simp] theorem Tx.keyed_o (KF : GoInterface → GoString) (x : Tx) : (x.keyed KF).o = x.o := rfl
@[simp] theorem Tx.keyed_t (KF : GoInterface → GoString) (x : Tx) : (x.keyed KF).t = x.t := rfl

end model

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`c.Transaction(txns...)`**, logically atomic, for writes `xs` (their keys ignored: the Go
`Transaction`s carry none) of the known types whose objects meet the store's contract `OK` and the
call's `D` (the key function's and the accessor's contracts, `keyOk D kf KF`, `rvAcc D rvOf`): no
error (a `nil` `*TransactionError`), the store `St.txn` of the writes keyed by `KF`. -/
abbrev cache.Transaction.spec : Prop :=
  ∀ (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF)
    (kf : GoFunc) (D : GoInterface → IProp GF) (KF : GoInterface → GoString)
    (rvOf : GoInterface → Option GoString) (sl : GoSlice) (dq : DFrac) (xs : List Tx),
  batchTyOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isCache ca ts γ OK Fam kf ∗
      keyOk D kf KF ∗ rvAcc D rvOf ∗ sl ↦*{dq} (xs.map Tx.txn) ∗ ⌜∀ x ∈ xs, x.typeOk⌝ ∗
      □ ([∗list] x ∈ xs, D x.o ∗ OK x.o) }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (Val (ca @!! go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty @!! go!"Transaction"))
      (Val #sl))
    @@ ∅
  <<{ storeSt γ (St.txn rvOf σ (xs.map (Tx.keyed KF))) }>>
  {{ RET #null; sl ↦*{dq} (xs.map Tx.txn) }}

end spec

end cache
end EtcdGrove
end Perennial
