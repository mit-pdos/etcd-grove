/- Lean-first (no Rocq counterpart). The proof of `testMiniboltConcurrent`: `Open` as in
`testMinibolt`, under the programs' predicate `valueOkP`, so that every transaction a reader sees
holds what `valueOk` accepts (`dbTx` carries `γ.vp`), whatever the writer has committed by then.
Each reader goroutine gets one of `Open`'s reader tokens and its cell of `results`, keeps a lower
bound `dbLast γ last` of the txid (so `last <= txid` holds), and gives the token and its cell,
holding true, back through the `WaitGroup` (Perennial's join idiom). The writer keeps the
committer's token at `(v - 1, v + 2)`; on an error it breaks. After `Wait`, `Close` gets every
reader token back. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.testMiniboltConcurrent
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__Get
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__Snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__Commit
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__Close
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.ProgramLemmas
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Done
public import Perennial.Spec.sync.WaitGroup__Wait
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

-- (as `lintest`'s `RunLemmas`)
theorem bigSepL_replicate_range' {A : Type} (n : Nat) (v : A) (Φ : Nat → A → IProp GF) :
    ([∗list] k ↦ x ∈ List.replicate n v, Φ k x) ⊢ [∗list] k ∈ List.range n, Φ k v := by
  induction n with
  | zero =>
    simp only [List.replicate_zero, List.range_zero]
    iintro _
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  | succ n ih =>
    rw [List.replicate_succ', List.range_succ]
    iintro H
    icases BigSepL.bigSepL_snoc.1 $$ H with ⟨H1, H2⟩
    iapply BigSepL.bigSepL_snoc.2
    isplitl [H1]
    · iapply ih $$ H1
    · rw [List.length_replicate]; iexact H2

/-- A slice of `n` copies of `v` as its elements' points-tos. -/
theorem ownSlice_replicate_elems' {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s : GoSlice) (n : Nat) (v : V) (dq : DFrac) :
    (s ↦*{dq} List.replicate n v : IProp GF) ⊢
      [∗list] c ∈ List.range n, typedPointsto (sliceIndexRef V ((c : Nat) : Int) s) v dq := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨Hsl, %Hl⟩)
  · have hn : n = 0 := by
      have := H.2; rw [List.replicate_eq_nil_iff] at this; exact this
    subst hn
    simp only [List.range_zero]
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  · icases typedPointsto_split _ _ _ $$ Hsl with Hsl
    simp only [TypedPointsto.typedPointstoDef]
    icases Hsl with ⟨%Hlen, Hsl⟩
    unfold arrayElems
    unfold sliceIndexRef
    iapply bigSepL_replicate_range' n v
      (fun (k : Nat) (x : V) => typedPointsto (GF := GF) (arrayIndexRef V (k : Int) s.ptr) x dq)
    iexact Hsl

theorem slice_len2 (sl : GoSlice)
    (h : (List.replicate 2 (zero_val Bool)).length = sint.nat sl.len ∧ 0 ≤ sint.Z sl.len) :
    sint.Z sl.len = 2 := by
  have h' : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
  have h1 := h.1
  simp only [List.length_replicate] at h1
  rw [h'] at h1; have := h.2; omega

theorem sint_nat_cast (k : w64) (h : 0 ≤ sint.Z k) : ((sint.nat k : Nat) : Int) = sint.Z k := by
  have h' : sint.nat k = (sint.Z k).toNat := rfl
  rw [h']; exact Int.toNat_of_nonneg h

theorem uintZ_le (a b : w64) (h : a.toNat ≤ b.toNat) : uint.Z a ≤ uint.Z b := by
  simp only [uint.Z]; omega

theorem sint_succ20 (i : w64) (h0 : 0 ≤ sint.Z i) (h : sint.Z i < 20) :
    0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ 20 := by
  constructor <;> word

theorem k_eq2 (k : w64) (h1 : sint.Z k ≤ 2) (h2 : ¬ sint.Z k < sint.Z (W64 2)) : sint.nat k = 2 := by
  have h' : sint.nat k = (sint.Z k).toNat := rfl
  have h3 : sint.Z (W64 2) = 2 := rfl
  rw [h']; rw [h3] at h2; omega

theorem le40 (x : w64) (h : uint.Z x ≤ uint.Z (W64 40)) : x.toNat ≤ 40 := by
  have h' : uint.Z (W64 40) = 40 := rfl
  simp only [uint.Z] at h h'; omega

theorem eq41 (x : w64) (h1 : x.toNat ≤ 41) (h : ¬ uint.Z x ≤ uint.Z (W64 40)) : x.toNat = 41 := by
  have h' : uint.Z (W64 40) = 40 := rfl
  have h2 : uint.Z x = (x.toNat : Int) := rfl
  rw [h', h2] at h; omega

theorem succ_toNat (x : w64) (h : x.toNat ≤ 40) : (x + W64 1).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofInt]; omega

set_option hygiene false in
/-- `testMiniboltConcurrent` after its writer loop (either exit): `Wait`, `Close`, and the
result. -/
local macro "mb_finish" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply (sync.join.WaitGroup.wp_Wait_of sync.WaitGroup.wp_Wait _ _ wg_ptr) $$ [Hwg] as ⟨Hres, -⟩
  · iframe Hwg
  (try wp_auto)
  rw [show List.range 2 = [0, 1] from rfl]
  icases BigSepL.bigSepL_cons.1 $$ Hres with ⟨Hd0, Hres⟩
  icases BigSepL.bigSepL_cons.1 $$ Hres with ⟨Hd1, -⟩
  unfold readerDone
  icases Hd0 with ⟨Hr0, Hc0⟩
  icases Hd1 with ⟨Hr1, Hc1⟩
  ihave Hrds := Hrds $$ Hr0 Hr1
  wp_apply wp_Close γ db _ _ $$ [Hown Hrds] as %e -
  · iframe; iframe #
  (try wp_auto)
  have hsl2 : sint.Z sl.len = 2 := slice_len2 sl Hsll
  have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
    rw [hsl2]; exact ⟨by decide, by decide⟩
  have hb1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z sl.len := by
    rw [hsl2]; exact ⟨by decide, by decide⟩
  rw [ite_eq_left hb0, show sint.Z (W64 0) = ((0 : Nat) : Int) from rfl]
  (try wp_auto)
  rw [ite_eq_left hb1, show sint.Z (W64 1) = ((1 : Nat) : Int) from rfl]
  (try wp_auto)
  iapply HΦ
  itrivial))

/-- What reader `i` gives back through the `WaitGroup`: its reader token, and its cell of
`results` holding true. -/
def readerDone (γ : DBNames) (db : Loc) (sl : GoSlice) (i : Nat) : IProp GF :=
  iprop(dbReader (GF := GF) γ db ∗ typedPointsto (sliceIndexRef Bool ((i : Nat) : Int) sl) true (DFrac.own 1))

/-- Two of the reader tokens, and the way back. -/
theorem reader_two (γ : DBNames) (db : Loc) :
    ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), dbReader (GF := GF) γ db) ⊢
      dbReader (GF := GF) γ db ∗ dbReader (GF := GF) γ db ∗ (dbReader (GF := GF) γ db -∗
        dbReader (GF := GF) γ db -∗
        [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), dbReader (GF := GF) γ db) := by
  have h : Int.toNat sync.rwmutex.actualMaxReaders = (Int.toNat sync.rwmutex.actualMaxReaders - 2) + 1 + 1 := by
    have : 2 < Int.toNat sync.rwmutex.actualMaxReaders := by
      rw [sync.rwmutex.actualMaxReaders_unseal]; decide
    omega
  rw [h, List.replicate_succ, List.replicate_succ]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H2⟩
  icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨H2, H3⟩
  iframe H1 H2
  iintro H1 H2
  iapply BigSepL.bigSepL_cons.2
  iframe H1
  iapply BigSepL.bigSepL_cons.2
  iframe

theorem testMiniboltConcurrent.wp_proof (wp_Open : Open.spec (GF := GF) (hG := hG))
    (wp_Get : DB.Get.spec (GF := GF) (hG := hG))
    (wp_Snapshot : DB.Snapshot.spec (GF := GF) (hG := hG))
    (wp_Commit : DB.Commit.spec (GF := GF) (hG := hG))
    (wp_Close : DB.Close.spec (GF := GF) (hG := hG))
    (wp_envFailure : envFailure.spec (GF := GF) (hG := hG))
    (wp_valueOk : valueOk.spec (GF := GF) (hG := hG)) :
    testMiniboltConcurrent.spec (GF := GF) (hG := hG) := by
  intro dir
  wp_start as ⟨#Hpkg, #Henv, #Hos, Hm⟩
  ihave Hf := dbFile_absent (dir ++ go!"/db") $$ Hm
  ihave #Hpkg' := Hpkg
  iunfold pkgFacts at Hpkg'
  icases Hpkg' with ⟨#Hsync, -⟩
  wp_auto
  wp_apply wp_Open (dir ++ go!"/db") 1 none 4 valueOkP (by simp [valueOkP]) $$ [Hf]
    as %db %err (⟨%Herr, %γ, %Hvp, #Hdb, -, Hown, #Hlast, -, Hrds⟩ | ⟨%Herr, -⟩)
  · iframe #; iframe
  rotate_left
  · obtain ⟨Herr, rfl⟩ := Herr
    cases err with
    | nil => exact absurd rfl Herr
    | ok ie =>
    (try wp_auto)
    wp_apply wp_envFailure $$ [Henv]
    · iframe #
    (try wp_auto)
    iapply HΦ
    itrivial
  subst Herr
  (try wp_auto)
  icases reader_two γ db $$ Hrds with ⟨Hrd0, Hrd1, Hrds⟩
  wp_apply (wp_slice_make2 (V := Bool) (W64 2)) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  ihave Hcells := ownSlice_replicate_elems' sl 2 (zero_val Bool) (DFrac.own 1) $$ Hsl
  ipersist db
  ipersist results
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr $$ wg with ⟨%γwg, Hwg⟩
  imod sync.join.init wg_ptr γwg $$ Hwg with Hwg
  ihave Hwg := sync.join.ownAdder_wand
    iprop([∗list] c ∈ List.range (sint.nat (W64 0)), readerDone γ db sl c)
    wg_ptr (W32 0) iprop(True) $$ [] Hwg
  · iintro _
    rw [show sint.nat (W64 0) = 0 from rfl, List.range_zero]
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro
  have H00 : sint.nat (W64 0) = 0 := rfl
  have H2 : sint.nat (W64 2) = 2 := rfl
  ihave Hcells : ([∗list] c ∈ List.range' (sint.nat (W64 0)) (2 - sint.nat (W64 0)),
      typedPointsto (sliceIndexRef Bool ((c : Nat) : Int) sl) false (DFrac.own 1) : IProp GF) $$ [Hcells]
  · rw [H00, Nat.sub_zero, ← List.range_eq_range']; iexact Hcells
  ihave Hrdl : ([∗list] c ∈ List.range' (sint.nat (W64 0)) (2 - sint.nat (W64 0)),
      dbReader (GF := GF) γ db : IProp GF) $$ [Hrd0 Hrd1]
  · rw [H00, Nat.sub_zero, show List.range' 0 2 = [0, 1] from rfl]
    iapply BigSepL.bigSepL_cons.2; iframe Hrd0
    iapply BigSepL.bigSepL_cons.2; iframe Hrd1
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  ihave HI : (∃ (k : w64) (na : w32),
      "r" ∷ r_ptr ↦ k ∗
      "Hwg" ∷ sync.join.ownAdder wg_ptr na ([∗list] c ∈ List.range (sint.nat k), readerDone γ db sl c) ∗
      "Hcells" ∷ ([∗list] c ∈ List.range' (sint.nat k) (2 - sint.nat k),
        typedPointsto (sliceIndexRef Bool ((c : Nat) : Int) sl) false (DFrac.own 1)) ∗
      "Hrdl" ∷ ([∗list] c ∈ List.range' (sint.nat k) (2 - sint.nat k), dbReader (GF := GF) γ db) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 2 ∧ sint.Z na = sint.Z k⌝ : IProp GF)
    $$ [r Hwg Hcells Hrdl]
  · iexists W64 0, W32 0
    iframe
    ipureintro
    exact ⟨by decide, by decide, by decide⟩
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z k < 2 := by have h := Hif; simp at h; exact h
    have hkn : sint.nat k < 2 := by word
    wp_apply (sync.join.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add
      (readerDone γ db sl (sint.nat k)) wg_ptr _ na) $$ [Hwg] as ⟨Hwg, Hdone⟩
    · iframe; iframe #; ipureintro; word
    rw [show 2 - sint.nat k = (2 - (sint.nat k + 1)) + 1 by omega, List.range'_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hcells with ⟨Hcell, Hcells⟩
    icases BigSepL.bigSepL_cons.1 $$ Hrdl with ⟨Hrdk, Hrdl⟩
    wp_apply wp_fork $$ [Hdone Hcell Hrdk]
    · (try wp_auto)
      wp_apply wp_with_defer as %defer defer
      (try wp_auto)
      ihave #Hl0 : dbLast (GF := GF) γ (zero_val w64 : w64).toNat $$ []
      · iunfold dbLast; iunfold dbLast at Hlast
        iapply (monoNatLbOwn_le (γ := γ.last) (n := 1) _ (by decide)) $$ Hlast
      ihave HJ : (∃ (i lst : w64), "i" ∷ i_ptr ↦ i ∗ "ok" ∷ ok_ptr ↦ true ∗ "last" ∷ last_ptr ↦ lst ∗
          "#Hl" ∷ dbLast (GF := GF) γ lst.toNat ∗ "Hrdk" ∷ dbReader (GF := GF) γ db ∗
          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ 20⌝ : IProp GF) $$ [i ok last Hrdk]
      · iexists W64 0, zero_val w64
        iframe; unfold named; iframe Hl0; ipureintro; exact ⟨by decide, by decide⟩
      have hsl2 : sint.Z sl.len = 2 := slice_len2 sl Hsll
      have hkb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := by
        refine ⟨Hk.1, ?_⟩; rw [hsl2]; exact Hlt
      have hkk : ((sint.nat k : Nat) : Int) = sint.Z k := sint_nat_cast k Hk.1
      rw [hkk]
      wp_for HJ
      wp_if_destruct
      · have Hlti : sint.Z i < 20 := by have h := Hif; simp at h; exact h
        wp_if_destruct
        wp_apply wp_Get γ db lst.toNat none $$ [Hrdk] as %txid %v %has %err ⟨Hrdk, -, Hres⟩
        · unfold dbOwnerOpt; iframe; try iframe #
        rotate_left
        wp_apply wp_Snapshot γ db lst.toNat none $$ [Hrdk] as %txid %v %has %err ⟨Hrdk, -, Hres⟩
        · unfold dbOwnerOpt; iframe; try iframe #
        all_goals (
          icases Hres with (⟨%Hok, #Hlt', #Htxr⟩ | %Herr)
          rotate_left
          · cases err with
            | nil => exact absurd rfl Herr
            | ok ie =>
            (try wp_auto)
            wp_apply wp_envFailure $$ [Henv]
            · iframe #
            (try wp_auto)
            rw [ite_eq_left hkb]
            (try wp_auto)
            wp_for_post
            wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done
              (readerDone γ db sl _) wg_ptr) $$ [Hdone Hrdk Hcell]
            · iframe Hdone; iframe #; unfold readerDone; rw [hkk]; iframe
            (try wp_auto)
            itrivial
          obtain ⟨rfl, Hle, -⟩ := Hok
          icases dbTx_vp γ _ _ $$ Htxr with %Hvt
          rw [Hvp] at Hvt
          (try wp_auto)
          wp_apply wp_valueOk txid v has as %b %Hb
          obtain rfl : b = true := Hb.mpr Hvt
          (try wp_auto)
          rw [decide_eq_true (uintZ_le lst txid Hle)]
          wp_for_post
          iframe
          iexists (i + W64 1), txid
          iframe
          unfold named
          iframe Hlt'
          ipureintro
          exact sint_succ20 i Hi.1 Hlti)
      · (try wp_auto)
        rw [ite_eq_left hkb]
        (try wp_auto)
        wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done
          (readerDone γ db sl _) wg_ptr) $$ [Hdone Hrdk Hcell]
        · iframe Hdone; iframe #; unfold readerDone; rw [hkk]; iframe
        (try wp_auto)
        itrivial
    wp_for_post
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    iframe
    iexists (k + W64 1), (na + W32 1)
    rw [hk1]
    iframe
    unfold named
    isplitl [Hwg]
    · iapply sync.join.ownAdder_wand $$ [] Hwg
      iintro ⟨H1, H2⟩
      rw [List.range_succ]
      iapply BigSepL.bigSepL_snoc.2
      iframe
    ipureintro
    refine ⟨by word, by word, by word⟩
  · have hk2 : sint.nat k = 2 := k_eq2 k Hk.2.1 Hif
    rw [hk2]
    iclear Hcells Hrdl
    ihave HW : (∃ x : w64, "v" ∷ v_ptr ↦ x ∗ "Hown" ∷ dbOwner (GF := GF) γ (x.toNat - 1) (x.toNat + 2) ∗
        "%Hx" ∷ ⌜2 ≤ x.toNat ∧ x.toNat ≤ 41⌝ : IProp GF) $$ [v Hown]
    · iexists W64 2
      rw [show (W64 2 : w64).toNat = 2 from rfl]
      iframe; unfold named; ipureintro; omega
    wp_for HW
    wp_if_destruct
    · have hx40 : x.toNat ≤ 40 := le40 x Hif
      wp_apply wp_Commit γ db (x.toNat - 1) (x.toNat + 2) x (by omega) (by omega)
          (by rw [Hvp]; exact valueOkP_next x Hx.1) $$ [Hown]
        as %e (⟨%He, Hown, -, -⟩ | ⟨%He, -, Hown⟩)
      · iframe #; iframe
      rotate_left
      · cases e with
        | nil => exact absurd rfl He
        | ok ie =>
        (try wp_auto)
        wp_apply wp_envFailure $$ [Henv]
        · iframe #
        (try wp_auto)
        wp_for_post
        mb_finish
      subst He
      (try wp_auto)
      wp_for_post
      iframe
      iexists (x + W64 1)
      rw [succ_toNat x hx40, show x.toNat + 1 - 1 = x.toNat - 1 + 1 by omega,
        show x.toNat + 1 + 2 = x.toNat + 2 + 1 by omega]
      iframe; unfold named; ipureintro; omega
    · have hx41 : x.toNat = 41 := eq41 x Hx.2 Hif
      mb_finish

end proof

end bboltfs
end EtcdGrove
end Perennial
