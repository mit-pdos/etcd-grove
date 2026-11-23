/-
`nodeArray` (exec.go) as a `sort.Interface`: its `Len`, `Less`, `Swap` over a slice of instance
pointers `ls` holding the ids `l` (pointers `ptrOf F`), the instances' `Seq`/`id` read from the
executor's view of the rows (`repInstsX`); `Less` is `keyLt` (`nodeArray_isSorter`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ExecPop

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof sort

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

theorem idx_lt_len (ii len : w64) (n : Nat) (h0 : 0 ≤ sint.Z ii) (hl : n = sint.nat len)
    (h : sint.nat ii < n) : sint.Z ii < sint.Z len := by
  subst hl; word

theorem keyLt_code (σ : RState) (a b : InstId) (sa sb : w32)
    (hsa : ((σ.inst a).map (·.seq)).getD 0 = sa) (hsb : ((σ.inst b).map (·.seq)).getD 0 = sb)
    (haq : a.q < nR) (hbq : b.q < nR) (hai : a.i < MAX_INSTANCE) (hbi : b.i < MAX_INSTANCE) :
    keyLt σ a b ↔ (sint.Z sa < sint.Z sb ∨
      (sa = sb ∧ sint.Z (W32 (a.q : Int)) < sint.Z (W32 (b.q : Int))) ∨
      (sa = sb ∧ W32 (a.q : Int) = W32 (b.q : Int) ∧
        sint.Z (W32 (a.i : Int)) < sint.Z (W32 (b.i : Int)))) := by
  unfold nR at haq hbq; unfold MAX_INSTANCE at hai hbi
  have e1 : sint.Z (W32 (a.q : Int)) = a.q := by word
  have e2 : sint.Z (W32 (b.q : Int)) = b.q := by word
  have e3 : sint.Z (W32 (a.i : Int)) = a.i := by word
  have e4 : sint.Z (W32 (b.i : Int)) = b.i := by word
  have e5 : W32 (a.q : Int) = W32 (b.q : Int) ↔ a.q = b.q := by
    constructor
    · intro h; have := congrArg sint.Z h; rw [e1, e2] at this; omega
    · intro h; rw [h]
  unfold keyLt; rw [hsa, hsb, e1, e2, e3, e4, e5]
  constructor
  · rintro (h | ⟨h1, h2 | ⟨h3, h4⟩⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, by omega⟩)
    · exact Or.inr (Or.inr ⟨h1, h3, by omega⟩)
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h3, h4⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl (by omega)⟩
    · exact Or.inr ⟨h1, Or.inr ⟨h3, by omega⟩⟩

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- The sorter's state: the slice `ls` holding the ids `l` (a permutation of `C`), the rows. -/
def naOwn (γ : EpNames) (i : Nat) (r : Loc) (F : Nat → List Loc) (σc : RState)
    (ix : InstId → Option (Nat × Nat)) (ls : GoSlice) (C : List InstId) (l : List InstId) :
    IProp GF :=
  iprop(⌜l.Perm C⌝ ∗ ls ↦* l.map (ptrOf F) ∗ repInstsX γ i r F σc.inst ix)

theorem nodeArray_isSorter (γ : EpNames) (i : Nat) (r : Loc) (F : Nat → List Loc) (σc : RState)
    (ix : InstId → Option (Nat × Nat)) (ls : GoSlice) (C : List InstId)
    (hC : ∀ x ∈ C, ∃ w, σc.inst x = some w) (hwf : ExecWf σc) :
    ⊢ pkgInit_epaxos (GF := GF) -∗ isSorter (GoInterfaceOk.mk epaxos.nodeArray.ty #ls)
      (naOwn γ i r F σc ix ls C) (keyLt σc) := by
  iintro #Hpk
  iapply isSorter_intro
  isplitr
  · iintro !> %l %Φ !> Hown HΦ
    dsimp only
    rw [method_unfold (t := epaxos.nodeArray.ty)]
    wp_auto
    unfold naOwn
    icases Hown with ⟨%Hp, Hs, Hins⟩
    ihave %Hl := ownSlice_len _ _ _ $$ Hs
    have : ls.len = W64 (l.length : Int) := by
      simp only [List.length_map] at Hl; have := Hl.1; have := Hl.2; word
    rw [this]
    iapply HΦ; iframe Hs Hins; ipureintro; exact Hp
  isplitr
  · iintro !> %l %ii %jj %a %b %Hij %Φ !> Hown HΦ
    dsimp only
    rw [method_unfold (t := epaxos.nodeArray.ty)]
    wp_auto
    obtain ⟨hi0, hj0, ha, hb⟩ := Hij
    unfold naOwn
    icases Hown with ⟨%Hp, Hs, Hins⟩
    ihave %Hl := ownSlice_len _ _ _ $$ Hs
    simp only [List.length_map] at Hl
    have hil : sint.nat ii < l.length := (List.getElem?_eq_some_iff.mp ha).1
    have hjl : sint.nat jj < l.length := (List.getElem?_eq_some_iff.mp hb).1
    have hbi : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z ls.len := ⟨hi0, idx_lt_len _ _ _ hi0 Hl.1 hil⟩
    have hbj : 0 ≤ sint.Z jj ∧ sint.Z jj < sint.Z ls.len := ⟨hj0, idx_lt_len _ _ _ hj0 Hl.1 hjl⟩
    have hla : (l.map (ptrOf F))[(sint.Z ii).toNat]? = some (ptrOf F a) := by
      rw [List.getElem?_map]; show Option.map _ l[sint.nat ii]? = _; rw [ha]; rfl
    have hlb : (l.map (ptrOf F))[(sint.Z jj).toNat]? = some (ptrOf F b) := by
      rw [List.getElem?_map]; show Option.map _ l[sint.nat jj]? = _; rw [hb]; rfl
    have haC : a ∈ C := Hp.mem_iff.mp (List.mem_of_getElem? ha)
    have hbC : b ∈ C := Hp.mem_iff.mp (List.mem_of_getElem? hb)
    obtain ⟨wa, hwa⟩ := hC a haC
    obtain ⟨wb, hwb⟩ := hC b hbC
    obtain ⟨haq, hai⟩ := hwf.ids a wa hwa
    obtain ⟨hbq, hbi'⟩ := hwf.ids b wb hwb
    by_cases hab : a = b
    · subst hab
      icases repInstsX_acc γ i r F σc.inst ix a haq (by omega) $$ Hins
        with ⟨%iss, %rows, %row, #Hiss, #Hrows, %Hrow, Hrow, %Hpa, Hxa, Hclose⟩
      rw [hwa]
      dsimp only [slotT, ownInstT, ownInstG]
      icases Hxa with ⟨%ya, Hya, %Hyfa, #Hida, Hresta⟩
      ihave #Hida' := Hida
      iStructNamed Hida'
      have hkey := keyLt_code σc a a ya.Seq' ya.Seq' (by rw [hwa, Hyfa.2.2.2.1]; rfl)
        (by rw [hwa, Hyfa.2.2.2.1]; rfl) haq haq (by omega) (by omega)
      repeat' (first
        | (simp only [hbi, hbj, _root_.and_self, ↓reduceIte]; first
          | (wp_apply wp_load_slice_index ls _ _ _ (ptrOf F a) hbi.1 $$ [$Hs] as Hs; (ipureintro; exact hla))
          | (wp_apply wp_load_slice_index ls _ _ _ (ptrOf F a) hbj.1 $$ [$Hs] as Hs; (ipureintro; exact hlb)))
        | wp_auto | wp_if_destruct)
      all_goals
        iapply HΦ
        isplitl [Hs Hya Hresta Hrow Hclose]
        · iframe Hs
          isplitr
          · ipureintro; exact Hp
          ihave Hins := Hclose $$ %(some wa) %(ix a) Hrow [Hya Hresta]
          · dsimp only; iexists ya; iframe Hya Hida Hresta; ipureintro; exact Hyfa
          rw [upd_self _ _ _ hwa, upd_self _ _ _ rfl]
          iexact Hins
        · ipureintro; rw [hkey]; simp only [true_iff, Bool.false_eq_true, false_iff]; grind
    · icases repInstsX_acc2 γ i r F σc.inst ix a b hab haq (by omega) hbq (by omega) $$ Hins
        with ⟨Hxa, Hxb, Hclose⟩
      rw [hwa, hwb]
      dsimp only [slotT, ownInstT, ownInstG]
      icases Hxa with ⟨%ya, Hya, %Hyfa, #Hida, Hresta⟩
      icases Hxb with ⟨%yb, Hyb, %Hyfb, #Hidb, Hrestb⟩
      ihave #Hida' := Hida
      ihave #Hidb' := Hidb
      iStructNamed Hida'
      iStructNamed Hidb'
      have hkey := keyLt_code σc a b ya.Seq' yb.Seq' (by rw [hwa, Hyfa.2.2.2.1]; rfl)
        (by rw [hwb, Hyfb.2.2.2.1]; rfl) haq hbq (by omega) (by omega)
      repeat' (first
        | (simp only [hbi, hbj, _root_.and_self, ↓reduceIte]; first
          | (wp_apply wp_load_slice_index ls _ _ _ (ptrOf F a) hbi.1 $$ [$Hs] as Hs; (ipureintro; exact hla))
          | (wp_apply wp_load_slice_index ls _ _ _ (ptrOf F b) hbj.1 $$ [$Hs] as Hs; (ipureintro; exact hlb)))
        | wp_auto | wp_if_destruct)
      all_goals
        iapply HΦ
        isplitl [Hs Hya Hyb Hresta Hrestb Hclose]
        · iframe Hs
          isplitr
          · ipureintro; exact Hp
          iapply Hclose $$ [Hya Hresta] [Hyb Hrestb]
          · iexists ya; iframe Hya Hida Hresta; ipureintro; exact Hyfa
          · iexists yb; iframe Hyb Hidb Hrestb; ipureintro; exact Hyfb
        · ipureintro; rw [hkey]; simp only [true_iff, Bool.false_eq_true, false_iff]; grind
  · iintro !> %l %ii %jj %a %b %Hij %Φ !> Hown HΦ
    dsimp only
    rw [method_unfold (t := epaxos.nodeArray.ty)]
    wp_auto
    obtain ⟨hi0, hj0, ha, hb⟩ := Hij
    unfold naOwn
    icases Hown with ⟨%Hp, Hs, Hins⟩
    ihave %Hl := ownSlice_len _ _ _ $$ Hs
    simp only [List.length_map] at Hl
    have hil : sint.nat ii < l.length := (List.getElem?_eq_some_iff.mp ha).1
    have hjl : sint.nat jj < l.length := (List.getElem?_eq_some_iff.mp hb).1
    have hbi : 0 ≤ sint.Z ii ∧ sint.Z ii < sint.Z ls.len := ⟨hi0, idx_lt_len _ _ _ hi0 Hl.1 hil⟩
    have hbj : 0 ≤ sint.Z jj ∧ sint.Z jj < sint.Z ls.len := ⟨hj0, idx_lt_len _ _ _ hj0 Hl.1 hjl⟩
    have hla : (l.map (ptrOf F))[(sint.Z ii).toNat]? = some (ptrOf F a) := by
      rw [List.getElem?_map]; show Option.map _ l[sint.nat ii]? = _; rw [ha]; rfl
    have hlb : (l.map (ptrOf F))[(sint.Z jj).toNat]? = some (ptrOf F b) := by
      rw [List.getElem?_map]; show Option.map _ l[sint.nat jj]? = _; rw [hb]; rfl
    repeat' (first
      | (simp only [hbi, hbj, _root_.and_self, ↓reduceIte]; first
        | (wp_apply wp_load_slice_index ls _ _ _ (ptrOf F a) hbi.1 $$ [$Hs] as Hs; (ipureintro; exact hla))
        | (wp_apply wp_load_slice_index ls _ _ _ (ptrOf F b) hbj.1 $$ [$Hs] as Hs; (ipureintro; exact hlb))
        | wp_auto)
      | wp_auto)
    wp_apply wp_store_slice_index ls (sint.Z ii) _ (ptrOf F b) $$ [$Hs] as Hs
    · ipureintro; refine ⟨hi0, ?_⟩; simp only [List.length_map, Hl.1]; have := hbi.2; have := Hl.2
      word
    wp_apply wp_store_slice_index ls (sint.Z jj) _ (ptrOf F a) $$ [$Hs] as Hs
    · ipureintro; refine ⟨hj0, ?_⟩; simp only [List.length_map, List.length_set, Hl.1]
      have := hbj.2; have := Hl.2; word
    iapply HΦ
    isplitr
    · ipureintro
      rw [swap_set_comm l (sint.nat ii) (sint.nat jj) a b ha hb]
      exact (slices.swap_perm l (sint.nat ii) (sint.nat jj) a b ha hb).symm.trans Hp
    iframe Hins
    rw [← List.map_set, ← List.map_set]
    iexact Hs
