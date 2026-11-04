/-
A live transaction's statistics for `TxStats`'s atomic methods (U5 of
`notes/bbolt-proof-plan.md`): `statsTok` opens `txsInv` at the statistics (`stats_open`), and
`sync/atomic`'s `AddInt64`/`LoadInt64` and bbolt's `atomicAddDuration`/`atomicLoadDuration` on a
field of them (`wp_stats_add`, ...).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Txn.Txs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section stats
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance BC.core_persistent (K : BC) : Persistent (K.core (GF := GF)) := by
  unfold BC.core; infer_instance

instance BC.full_persistent (K : BC) : Persistent (K.full (GF := GF)) := by
  unfold BC.full isBoltP; infer_instance

/-- **A live transaction's statistics**, for the holder of its statistics' token. -/
theorem stats_open (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (E : CoPset)
    (hE : ↑(txsN K.N) ⊆ E) :
    K.core (GF := GF) ∗ reg tx K.B r ∗ statsTok r m q ⊢
    |={E, E \ ↑(txsN K.N)}=> ∃ s : TxStats, tx.[Tx, go!"stats"] ↦ s ∗
      (∀ s' : TxStats, tx.[Tx, go!"stats"] ↦ s' ={E \ ↑(txsN K.N), E}=∗ statsTok r m q) := by
  iintro ⟨#Hc, #Hreg, Ht⟩
  unfold BC.core isBoltCoreP
  icases Hc with ⟨-, -, -, -, -, -, -, -, -, -, #Hinv⟩
  unfold statsTok
  cases m
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iapply txs_stats_done K.B K.N K.p K.sp K.t0 E hE tx r
    iframe Hinv Hreg Ht
  · simp only [↓reduceIte]
    iapply txs_stats_atomic' K.B K.N K.p K.sp K.t0 E hE tx r q
    iframe Hinv Hreg Ht

variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `atomicAddDuration(ptr, du)` is `AddInt64` on the duration's cell: logically atomic. -/
theorem wp_atomicAddDuration (ptr : Loc) (du : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt -∗
    (|={⊤,∅}=> ▷ ∃ v : w64, ptr ↦ v ∗ (ptr ↦ (v + du) ={∅,⊤}=∗ Φ #(v + du))) -∗
    WP (App (App (Val #(functions atomicAddDuration [])) (Val #ptr)) (Val #du)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core sync.atomic.wp_AddInt64 $$ [] [HΦ «$res0»]
  · iPkgInit
  imod HΦ with ⟨%v, Hp, HΦ⟩
  imodintro; inext
  iexists v
  iframe Hp
  iintro Hp
  imod HΦ $$ Hp with HΦ
  imodintro
  wp_auto
  iexact HΦ

/-- `atomicLoadDuration(ptr)` is `LoadInt64` on the duration's cell: logically atomic. -/
theorem wp_atomicLoadDuration (ptr : Loc) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt -∗
    (|={⊤,∅}=> ▷ ∃ v : w64, ptr ↦ v ∗ (ptr ↦ v ={∅,⊤}=∗ Φ #v)) -∗
    WP (App (Val #(functions atomicLoadDuration [])) (Val #ptr)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core sync.atomic.wp_LoadInt64 $$ [] [HΦ «$res0»]
  · iPkgInit
  imod HΦ with ⟨%v, Hp, HΦ⟩
  imodintro; inext
  iexists v
  iframe Hp
  iintro Hp
  imod HΦ $$ Hp with HΦ
  imodintro
  wp_auto
  iexact HΦ

end stats
end bbolt
end EtcdGrove
end Perennial
