/-
`Tx.init` and `newBucket` (U5 of `notes/bbolt-proof-plan.md`): a fresh transaction's fields from
the current meta (`DB.meta`, `Meta.Copy`), its root bucket from the meta's root.
-/
module

public import Spec.go_etcd_io.bbolt.DB__meta
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Copy
public import Spec.go_etcd_io.bbolt.internal.common.Meta__RootBucket
public import Spec.go_etcd_io.bbolt.internal.common.Meta__IncTxid
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import Proof.go_etcd_io.bbolt.Txn.MetaAlloc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `newBucket(tx)`'s value: the transaction, the default fill percent, its maps. -/
def newBucketV (tx bm nm : Loc) : go_etcd_io.bbolt.Bucket :=
  { InBucket' := null, tx' := tx, buckets' := bm, page' := null, rootNode' := null,
    nodes' := nm, FillPercent' := W64 4602678819172646912 }

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx hos in
theorem fill_default_not_nan : ¬ float64IsNaN (W64 4602678819172646912) := by
  decide

omit hos in
theorem wp_newBucket (tx : Loc) (dq : DFrac) (w : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ tx.[Tx, go!"writable"] ↦{dq} w }}
      (App (Val #(functions newBucket [])) (Val #tx))
    {{ (bm nm : Loc), RET #(newBucketV tx bm nm); tx.[Tx, go!"writable"] ↦{dq} w ∗
        (if w then iprop(bm ↦$ (∅ : GMap GoString Loc) ∗ nm ↦$ (∅ : GMap w64 Loc))
         else iprop(⌜bm = null ∧ nm = null⌝)) }} := by
  wp_start as Hw
  unfold newBucketV
  wp_auto
  cases w
  · wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
    try (ipureintro; trivial)
  · wp_auto
    wp_apply (wp_map_make1 (K := GoString) (V := Loc)) as %bm Hbm
    wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %nm Hnm
    iapply HΦ
    simp only [↓reduceIte]
    iframe

/-- The meta `Tx.init` copies, for a writable transaction its txid one more. -/
def initMeta (w : Bool) (mv : Meta) : Meta := if w then { mv with txid' := mv.txid' + 1 } else mv

/-- The root bucket `Tx.init` makes: `newBucket`'s, with its header `ibp`. -/
def initRoot (tx bm nm ibp : Loc) : go_etcd_io.bbolt.Bucket :=
  { (newBucketV tx bm nm) with InBucket' := ibp }

omit hos in
/-- The current meta of the meta cells (what `db.meta()` points to), typed, and back. -/
theorem metaCells_cur_acc (b : Loc) (l : Nat) (C : CommitSt) (q : Qp) (hok : C.metaOk) :
    metaCellsQ (GF := GF) q (some (b, l) : MapSt) C ⊢
      (b +ₗ ((16 + 4096 * (C.txid % 2) : Nat) : Int)) ↦{DFrac.own q} metaOf (C.slot C.txid) ∗
      ((b +ₗ ((16 + 4096 * (C.txid % 2) : Nat) : Int)) ↦{DFrac.own q} metaOf (C.slot C.txid) -∗
        metaCellsQ q (some (b, l) : MapSt) C) := by
  obtain ⟨hl0, hl1, -⟩ := hok
  simp only [metaCellsQ]
  iintro ⟨H0, H1⟩
  rcases Nat.mod_two_eq_zero_or_one C.txid with hT | hT
  · have hs : C.slot C.txid = C.m0 := by unfold CommitSt.slot; simp [hT]
    rw [hs, show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = ((16 : Nat) : Int) by simp [hT]]
    ihave %Hp0 := bytesPointsto_pos _ _ _ (by intro h; rw [h] at hl0; simp at hl0) $$ H0
    icases bytesPointsto_view_read (V := Meta) b (DFrac.own q) C.m0 16 _ rfl (by omega) Hp0
      $$ H0 with ⟨M0, C0⟩
    rw [show (decode ((C.m0.drop 16).take 64) : Meta) = metaOf C.m0 from rfl]
    iframe M0
    iintro M0
    ihave H0 := C0 $$ M0
    iframe
  · have hs : C.slot C.txid = C.m1 := by unfold CommitSt.slot; simp [hT]
    rw [hs, show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = (4096 : Int) + ((16 : Nat) : Int) by
      simp [hT], ← loc_add_assoc]
    ihave %Hp1 := bytesPointsto_pos _ _ _ (by intro h; rw [h] at hl1; simp at hl1) $$ H1
    icases bytesPointsto_view_read (V := Meta) (b +ₗ (4096 : Int)) (DFrac.own q) C.m1 16 _ rfl
      (by omega) Hp1 $$ H1 with ⟨M1, C1⟩
    rw [show (decode ((C.m1.drop 16).take 64) : Meta) = metaOf C.m1 from rfl]
    iframe M1
    iintro M1
    ihave H1 := C1 $$ M1
    iframe

omit hos in
theorem wp_Tx_init (wp_meta : DB.meta.spec (GF := GF) (hG := hG))
    (wp_Copy : internal.common.Meta.Copy.spec (GF := GF) (hG := hG))
    (wp_RootBucket : internal.common.Meta.RootBucket.spec (GF := GF) (hG := hG))
    (wp_IncTxid : internal.common.Meta.IncTxid.spec (GF := GF) (hG := hG))
    (tx db b : Loc) (l : Nat) (C : CommitSt) (dq : DFrac) (q : Qp) (w : Bool) (d0 m0 p0 : Loc)
    (r0 : go_etcd_io.bbolt.Bucket) (hok : C.metaOk) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ tx.[Tx, go!"writable"] ↦ w ∗
        tx.[Tx, go!"db"] ↦ d0 ∗ tx.[Tx, go!"meta"] ↦ m0 ∗ tx.[Tx, go!"root"] ↦ r0 ∗
        tx.[Tx, go!"pages"] ↦ p0 ∗
        mapFields db dq (some (b, l) : MapSt) ∗ metaCellsQ q (some (b, l) : MapSt) C }}
      (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"init")) (Val #db))
    {{ (m ibp bm nm pm : Loc), RET #();
        tx.[Tx, go!"writable"] ↦ w ∗ tx.[Tx, go!"db"] ↦ db ∗ tx.[Tx, go!"meta"] ↦ m ∗
        tx.[Tx, go!"root"] ↦ initRoot tx bm nm ibp ∗ tx.[Tx, go!"pages"] ↦ pm ∗
        m ↦ initMeta w (metaOf (C.slot C.txid)) ∗ ibp ↦ (metaOf (C.slot C.txid)).root' ∗
        (if w then iprop(pm ↦$ (∅ : GMap w64 Loc) ∗ bm ↦$ (∅ : GMap GoString Loc) ∗
            nm ↦$ (∅ : GMap w64 Loc))
         else iprop(⌜pm = null ∧ bm = null ∧ nm = null⌝)) ∗
        mapFields db dq (some (b, l) : MapSt) ∗ metaCellsQ q (some (b, l) : MapSt) C ∗
        ⌜0 < m.addr⌝ }} := by
  wp_start as ⟨Hw, Hdb, Hm, Hr, Hp, Hmf, Hmc⟩
  wp_pures
  wp_alloc_auto
  wp_pures
  wp_alloc_auto
  repeat (wp_pures; first | wp_load | wp_store)
  wp_pures
  wp_apply +noauto Meta.wp_alloc_pos as %mp ⟨Hmp, %Hmpos⟩
  wp_auto
  wp_apply wp_meta db b l C dq q hok $$ [Hmf Hmc] as ⟨Hmf, Hmc⟩
  · iframe
  icases metaCells_cur_acc b l C q hok $$ Hmc with ⟨Hc, Hcl⟩
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_apply wp_Copy _ _ _ _ _ $$ [Hc Hmp] as ⟨Hc, Hmv⟩
  · iframe
  ihave Hmc := Hcl $$ Hc
  generalize metaOf (C.slot C.txid) = mv
  wp_apply wp_newBucket tx (DFrac.own 1) w $$ [Hw] as %bm %nm ⟨Hw, Hmaps⟩
  · iframe
  wp_apply wp_RootBucket $$ [Hpkc]
  unfold initRoot newBucketV initMeta
  cases w
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hmaps with %Hbn
    obtain ⟨rfl, rfl⟩ := Hbn
    wp_auto
    iapply HΦ
    iframe
    ipureintro; exact ⟨⟨rfl, rfl, rfl⟩, Hmpos⟩
  · simp only [↓reduceIte]
    wp_auto
    wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %pm Hpm
    wp_apply wp_IncTxid $$ [Hpkc Hmv] as Hmv
    · iframe
    iapply HΦ
    iframe
    ipureintro; exact Hmpos

end proof

end bbolt
end EtcdGrove
end Perennial
