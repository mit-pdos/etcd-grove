/-
`DB.freepages`' scan (U10e of `notes/bbolt-proof-plan.md`): the ids of `[2, i)` not covered,
as the loop builds them (`freeIdsBelow`), the loop condition's `db.meta().Pgid()`, and the
mapping fields out of the reader.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.CheckSpec
public import Proof.go_etcd_io.bbolt.Commit.FreepagesIds
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Pgid
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

open Classical in
/-- The ids of `[2, i)` no page of `C` covers, increasing (the scan's `fids` before `i`). -/
def freeIdsBelow (C : CommitSt) (i : Nat) : List w64 :=
  ((List.range' 2 (i - 2)).filter fun x => decide (¬ coversSlot C.pages x)).map
    fun (x : Nat) => W64 (x : Int)

theorem freeIdsBelow_two (C : CommitSt) : freeIdsBelow C 2 = [] := by
  simp [freeIdsBelow]

open Classical in
theorem freeIdsBelow_succ (C : CommitSt) (i : Nat) (h : 2 ≤ i) :
    freeIdsBelow C (i + 1) = freeIdsBelow C i ++
      (if coversSlot C.pages i then [] else [W64 (i : Int)]) := by
  unfold freeIdsBelow
  have : i + 1 - 2 = (i - 2) + 1 := by omega
  rw [this, List.range'_1_concat, List.filter_append, List.map_append]
  congr 1
  have h2 : 2 + (i - 2) = i := by omega
  rw [h2]
  by_cases hc : coversSlot C.pages i <;> simp [hc]

theorem freeIdsBelow_hwm (C : CommitSt) : freeIdsBelow C C.hwm = freeIdsOf C := rfl

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit hos in
/-- **`db.meta().Pgid()`**: the current meta's high-water mark. -/
theorem wp_meta_Pgid (wp_Pgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (b : Loc) (l : Nat) (C : CommitSt) (q : Qp) (hok : C.metaOk) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗
        metaCellsQ q (some (b, l) : MapSt) C }}
      (App (Val ((b +ₗ ((16 + 4096 * (C.txid % 2) : Nat) : Int)) @!! go.GoType.PointerType Meta.ty
        @!! go!"Pgid")) (Val #()))
    {{ RET #(W64 (C.hwm : Int)); metaCellsQ q (some (b, l) : MapSt) C }} := by
  iintro %Φ ⟨#Hpkc, Hmc⟩ HΦ
  obtain ⟨hl0, hl1, -, -, -, -, ⟨-, -, hpg, -⟩, -⟩ := hok
  have hpg' : ∀ v : Meta, v.pgid'.toNat = C.hwm → v.pgid' = W64 (C.hwm : Int) := by
    intro v hv; apply BitVec.eq_of_toNat_eq; rw [← hv]; simp
  simp only [metaCellsQ]
  icases Hmc with ⟨H0, H1⟩
  rcases Nat.mod_two_eq_zero_or_one C.txid with hT | hT
  · unfold CommitSt.slot at hpg
    simp only [hT, ↓reduceIte] at hpg
    rw [show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = ((16 : Nat) : Int) by simp [hT]]
    ihave %Hp0 := bytesPointsto_pos _ _ _ (by intro h; rw [h] at hl0; simp at hl0) $$ H0
    icases bytesPointsto_view_read (V := Meta) b (DFrac.own q) C.m0 16 _ rfl (by omega) Hp0
      $$ H0 with ⟨M0, C0⟩
    rw [show (decode ((C.m0.drop 16).take 64) : Meta) = metaOf C.m0 from rfl]
    rw [← hpg' _ hpg]
    generalize metaOf C.m0 = v0
    wp_apply wp_Pgid _ v0 (DFrac.own q) $$ [M0] as M0
    · iframe
    ihave H0 := C0 $$ M0
    iapply HΦ; iframe
  · unfold CommitSt.slot at hpg
    simp only [show C.txid % 2 ≠ 0 by omega, ↓reduceIte] at hpg
    rw [show ((16 + 4096 * (C.txid % 2) : Nat) : Int) = (4096 : Int) + ((16 : Nat) : Int) by
      simp [hT], ← loc_add_assoc]
    ihave %Hp1 := bytesPointsto_pos _ _ _ (by intro h; rw [h] at hl1; simp at hl1) $$ H1
    icases bytesPointsto_view_read (V := Meta) (b +ₗ (4096 : Int)) (DFrac.own q) C.m1 16 _ rfl
      (by omega) Hp1 $$ H1 with ⟨M1, C1⟩
    rw [show (decode ((C.m1.drop 16).take 64) : Meta) = metaOf C.m1 from rfl]
    rw [← hpg' _ hpg]
    generalize metaOf C.m1 = v1
    wp_apply wp_Pgid _ v1 (DFrac.own q) $$ [M1] as M1
    · iframe
    ihave H1 := C1 $$ M1
    iapply HΦ; iframe

omit package_sem in
/-- **The reader's mapping fields**, out of `rdTxK` (at some share) and back, with the mapping
named by the caller's half of `B.map`. -/
theorem rdTxK_mapFields_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (qm : Qp) (ms : MapSt) :
    rdTxK (GF := GF) K tx src q T v ∗ ghostVar K.B.map qm ms ⊢ ∃ dq l,
      ⌜ms = some (v.base, l)⌝ ∗ mapFields K.db dq (some (v.base, l) : MapSt) ∗
      ghostVar K.B.map qm ms ∗
      (mapFields K.db dq (some (v.base, l) : MapSt) -∗ rdTxK K tx src q T v) := by
  unfold rdTxK rtxFrac
  iintro ⟨⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpk, #Hcore, Hv, Hex,
    ⟨%t, Hw, Hm, Hmeta, Hroot, Hfill, Hpages, Hch, Hwf, Hdb, Hmv, Hcells,
      ⟨%l, Hg, Hmf, %Hl⟩, Hvo, %Hf⟩, Hpool⟩, Hgm⟩
  icombine Hg Hgm gives % ⟨_, hms⟩
  have hdb : r.db = K.db := Hc.2.1
  iexists _, l
  isplitr
  · ipureintro; exact hms.symm
  rw [← hdb]
  iframe Hmf Hgm
  iintro Hmf
  iexists r, c, mv, k
  iframe; iframe #
  isplitr
  · ipureintro; exact ⟨Hc.1, rfl, Hc.2.2⟩
  ipureintro; exact ⟨Hl, Hf⟩

end proof

end bbolt
end EtcdGrove
end Perennial
