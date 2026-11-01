/- Lean-first (no Rocq counterpart). The end of `commit`, under `metalock`, with the meta cells out
of the mapping's invariant: publishing the new meta pages and the new committed page
(`metas_publish`), or failing the handle (`meta_fail`). -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Writer

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- The committed pages up to `hwm + 1`: those up to `hwm`, and page `hwm`. -/
theorem pages_snoc (P : Nat → IProp GF) (hwm : Nat) (h2 : 2 ≤ hwm) :
    ([∗list] r ∈ List.range' 2 (hwm - 2), P r) ∗ P hwm ⊢
      [∗list] r ∈ List.range' 2 (hwm + 1 - 2), P r := by
  rw [show hwm + 1 - 2 = (hwm - 2) + 1 by omega, List.range'_concat,
    show 2 + 1 * (hwm - 2) = hwm by omega]
  iintro ⟨H, Hp⟩
  iapply (BigSepL.bigSepL_snoc (Φ := fun _ r => P r)).2
  iframe

/-- Publishing a commit (the writer holds both mutexes, and its half of the invariant's token, so
the invariant is open): the meta pages `mp'` and the high water mark `hwm + 1`, the meta cells back
in the invariant holding the metas of `mp'`, unlent, and page `hwm` committed (`B`), its cells
into the invariant, unlent under its fresh loan key `hwm`. -/
theorem metas_publish (γ : DBNames) (p : GoString) (base : Loc) (len : Nat) (γm : GName)
    (mp mp' : List w8) (hwm : Nat) (B : List w8) (hl : 4096 * (hwm + 1) ≤ len) (h2 : 2 ≤ hwm)
    (hmp' : mp'.length = 8192) :
    mapInv (GF := GF) γ p base len γm ∗ ghostVar γm (1 : Qp).half () ∗
      ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗ ghostVar γ.cur (1 : Qp).half (mp, false, hwm) ∗
      ghostVar γ.out (1 : Qp).half.half true ∗ ghostVar γ.out (1 : Qp).half.half true ∗
      cellsB (GF := GF) base 16 ((mp'.drop 16).take 64) ∗
      cellsB (GF := GF) base 4112 ((mp'.drop 4112).take 64) ∗
      pageIs (GF := GF) p hwm B ∗ cellsB (GF := GF) base (4096 * hwm) B ⊢
      |={⊤}=> ghostVar γm (1 : Qp).half () ∗ ghostVar γ.cur (1 : Qp).half.half (mp', false, hwm + 1) ∗
        ghostVar γ.cur (1 : Qp).half (mp', false, hwm + 1) ∗
        ghostVar γ.out (1 : Qp).half.half false ∗ ghostVar γ.out (1 : Qp).half.half false := by
  iintro ⟨#Hinv, Htok, Hcur, Hcm, Ho1, Ho2, Hc0, Hc1, #HB, HBc⟩
  unfold mapInv
  icases Hinv with ⟨%_, %γl, #Hinv⟩
  imod inv_acc (by simp) $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with (>Hc | >Htok2)
  rotate_left
  · icombine Htok Htok2 gives % ⟨Hbad, _⟩
    exfalso
    have h : 0 < ((1 : Qp).half).val := ((1 : Qp).half).2
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one] at Hbad
    grind
  unfold mapLend
  icases Hc with ⟨%mp2, %fl2, %hwm2, %K, Hcur2, %Hl, Ha, %HK, Hpages, Hmo⟩
  icombine Hcur Hcur2 gives % ⟨_, Heq⟩
  cases Heq
  -- `cur`
  ihave Hc := (ghostVar_split_half γ.cur (1 : Qp).half (mp, false, hwm)).2 $$ [Hcur Hcur2]
  · iframe
  imod ghostVar_update_halves (mp', false, hwm + 1) γ.cur _ _ $$ Hc Hcm with ⟨Hc, Hcm⟩
  icases (ghostVar_split_half γ.cur (1 : Qp).half (mp', false, hwm + 1)).1 $$ Hc with ⟨Hcur, Hcur2⟩
  -- `out`
  ihave Ho := (ghostVar_split_half γ.out (1 : Qp).half true).2 $$ [Ho1 Ho2]
  · iframe
  icases Hmo with (⟨Hout, %mc2, Hk⟩ | ⟨Hout, %mc2, -, -⟩)
  rotate_left
  · icombine Ho Hout gives % ⟨_, Hbad⟩; cases Hbad
  imod ghostVar_update_halves false γ.out true true $$ Ho Hout with ⟨Ho, Hout⟩
  icases (ghostVar_split_half γ.out (1 : Qp).half false).1 $$ Ho with ⟨Ho1, Ho2⟩
  -- page `hwm`'s loan key, then the metas'
  imod ghost_map_insert (V := List w8) hwm B (HK hwm (by omega) (Nat.le_refl _)) $$ Ha with ⟨Ha, Hkp⟩
  imod ghost_map_update (V := List w8) ((mp'.drop 16).take 64 ++ (mp'.drop 4112).take 64) $$ Ha Hk with ⟨Ha, Hk⟩
  ihave HBc := (cellsB_bytes base B (4096 * hwm)).1 $$ HBc
  ihave Hlent := lent_intro (GF := GF) γm γl hwm (base +ₗ ((4096 * hwm : Nat) : Int)) B $$ [Hkp HBc]
  · iframe
  ihave Hpages := pages_snoc (fun r => iprop(∃ B, pageIs (GF := GF) p r B ∗
      lentCells (GF := GF) γm γl r (base +ₗ ((4096 * r : Nat) : Int)) B)) hwm h2 $$ [Hpages Hlent]
  · iframe Hpages
    iexists B
    iframe Hlent
    iexact HB
  have hl1 : ((mp'.drop 16).take 64).length = 64 := by simp; omega
  have ht : ((mp'.drop 16).take 64 ++ (mp'.drop 4112).take 64).take 64 = (mp'.drop 16).take 64 := List.take_left' hl1
  have hd : ((mp'.drop 16).take 64 ++ (mp'.drop 4112).take 64).drop 64 = (mp'.drop 4112).take 64 := List.drop_left' hl1
  imod Hclose $$ [Hcur2 Ha Hpages Hout Hk Hc0 Hc1] with _
  · inext; ileft
    iexists mp', false, hwm + 1, (K.insert hwm B).insert 0 ((mp'.drop 16).take 64 ++ (mp'.drop 4112).take 64)
    iframe
    isplitr; · ipureintro; exact hl
    isplitr
    · ipureintro; intro k hk hh
      show ((K.insert hwm B).insert 0 ((mp'.drop 16).take 64 ++ (mp'.drop 4112).take 64)) !! k = none
      rw [GMap.lookup_insert_ne _ _ (by omega)]
      show (K.insert hwm B) !! k = none
      rw [GMap.lookup_insert_ne _ _ (by omega)]
      exact HK k hk (by omega)
    iright; iframe Hout
    iexists (mp'.drop 16).take 64 ++ (mp'.drop 4112).take 64
    isplitr
    · ipureintro
      refine ⟨?_, fun _ => rfl⟩
      simp; omega
    unfold metaLent metaBytes
    ileft; iframe Hk
    rw [ht, hd]
    isplitl [Hc0]
    · iapply (cellsB_bytes base _ 16).1; iexact Hc0
    · iapply (cellsB_bytes base _ 4112).1; iexact Hc1
  imodintro
  iframe

/-- Failing the handle in `commit` (under `metalock`, `failed` stored): the meta pages' state
failed, the meta cells back in the invariant holding whatever the failed write left (`mc`),
`metaR`'s failed branch with half of the meta pages' bytes `X` and its half of `own`, and
`dbFailed`. -/
theorem meta_fail (γ : DBNames) (db : Loc) (p : GoString) (base : Loc) (len : Nat) (γm : GName)
    (mp : List w8) (hwm : Nat) (mc : List w8) (hmc : mc.length = 128) (X : List (w8 × Bool))
    (hX : X.length = 8192) (T : GMap Nat (Option w64)) (x : Nat × Nat) :
    mapInv (GF := GF) γ p base len γm ∗ ghostVar γm (1 : Qp).half () ∗
      ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗ ghostVar γ.cur (1 : Qp).half (mp, false, hwm) ∗
      ghostVar γ.out (1 : Qp).half.half true ∗ ghostVar γ.out (1 : Qp).half.half true ∗
      cellsB (GF := GF) base 16 (mc.take 64) ∗ cellsB (GF := GF) base 4112 (mc.drop 64) ∗
      db.[DB, go!"failed"] ↦ true ∗ monoNatAuthOwn γ.fail 1 0 ∗ ghostMapAuth γ.txs 1 T ∗
      ghostVar γ.own (1 : Qp).half x ∗ ghostVar γ.cls (1 : Qp).half false ∗
      osBytes (GF := GF) p 0 (DFrac.own (1 : Qp).half) X ⊢
      |={⊤}=> metaR (GF := GF) γ db p ∗ dbFailed (GF := GF) γ ∗ ghostVar γm (1 : Qp).half () ∗
        ghostVar γ.cur (1 : Qp).half.half (mp, true, hwm) ∗ ghostVar γ.out (1 : Qp).half.half false := by
  iintro ⟨#Hinv, Htok, Hcur, Hcm, Ho1, Ho2, Hc0, Hc1, Hfl, Hfail, Hauth, Hown, Hcls, HX⟩
  imod fail_cur_inv γ p base len γm mp hwm $$ [Htok Hcur Hcm] with ⟨Htok, Hcur, Hcm⟩
  · iframe; iframe #
  imod metas_in γ p base len γm mp true hwm mc hmc (fun h => by cases h)
    $$ [Htok Hcur Ho1 Ho2 Hc0 Hc1] with ⟨Htok, Hcur, Ho1, Ho2⟩
  · iframe; iframe #
  imod mono_nat_own_update 1 (by omega) $$ Hfail with ⟨Hfail, Hlb⟩
  imodintro
  iframe Htok Hcur Ho1
  isplitr [Hlb]
  · unfold metaR
    iexists true, mp, X.map Prod.fst, hwm, X, T
    iframe
    isplitl [HX Hcls]
    · ileft; iframe
    isplitr
    · ipureintro; exact ⟨hX, rfl⟩
    dsimp only
    iframe Hfail
    iexists x; iexact Hown
  · unfold dbFailed; iexact Hlb

end lemmas

end bboltfs
end EtcdGrove
end Perennial
