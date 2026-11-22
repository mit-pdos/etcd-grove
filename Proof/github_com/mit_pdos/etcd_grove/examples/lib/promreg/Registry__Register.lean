/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/promreg/Registry__Register.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.promreg.Registry__Register
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
open _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lib

section helpers
variable [GooseExts]

/-! ### The loop's pure state -/

/-- The distinct IDs of the first `j` descriptors, in order (`newIDs` after `j` iterations). -/
def promreg.pIDs (ds : List promreg.Desc) (j : Nat) : List w64 := ((ds.take j).map (·.ID')).eraseDups

theorem promreg.mem_pIDs (ds : List promreg.Desc) (j : Nat) (k : w64) :
    k ∈ promreg.pIDs ds j ↔ k ∈ (ds.take j).map (·.ID') := by
  unfold promreg.pIDs; exact List.mem_eraseDups

theorem promreg.pIDs_succ (ds : List promreg.Desc) (j : Nat) (d : promreg.Desc) (h : ds[j]? = some d) :
    promreg.pIDs ds (j + 1) =
      if d.ID' ∈ promreg.pIDs ds j then promreg.pIDs ds j else promreg.pIDs ds j ++ [d.ID'] := by
  have ht : ds.take (j + 1) = ds.take j ++ [d] := by
    rw [List.take_add_one, h]; rfl
  have hm := promreg.mem_pIDs ds j d.ID'
  unfold promreg.pIDs at *
  rw [ht, List.map_append, List.eraseDups_append]
  by_cases hd : d.ID' ∈ (ds.take j).map (·.ID')
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (hm.2 hd))]
    rw [List.map_take] at hd
    simp [List.removeAll, hd]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => hd (hm.1 h')))]
    rw [List.map_take] at hd
    simp [List.removeAll, hd]
    rfl

theorem promreg.pIDs_all (ds : List promreg.Desc) :
    promreg.pIDs ds ds.length = (ds.map (·.ID')).eraseDups := by
  unfold promreg.pIDs; rw [List.take_length]

/-- The XOR of a list of IDs (`collectorID`). -/
def promreg.xorAll (ks : List w64) : w64 := ks.foldl (· ^^^ ·) 0

theorem promreg.xorAll_snoc (ks : List w64) (k : w64) :
    promreg.xorAll (ks ++ [k]) = promreg.xorAll ks ^^^ k := by
  unfold promreg.xorAll; rw [List.foldl_append]; rfl

theorem promreg.mem_descKeys (ds : List promreg.Desc) (k : w64) :
    k ∈ promreg.descKeys ds ↔ k ∈ promreg.pIDs ds ds.length ∨ k = promreg.xorAll (promreg.pIDs ds ds.length) := by
  rw [promreg.pIDs_all]
  unfold promreg.descKeys promreg.xorAll
  by_cases hc : (ds.map (·.ID')).eraseDups.foldl (· ^^^ ·) 0 ∈ (ds.map (·.ID')).eraseDups
  · simp only [hc, ite_true]
    constructor
    · exact Or.inl
    · rintro (h | rfl) <;> assumption
  · simp only [hc, ite_false, List.mem_append, List.mem_singleton]

theorem promreg.lookup_union_none {V : Type} (m1 m2 : GMap w64 V) (k : w64) (h : (m1 ∪ m2) !! k = none) :
    m1 !! k = none ∧ m2 !! k = none := by
  rw [gmap_lookup_union] at h
  cases h1 : m1 !! k <;> cases h2 : m2 !! k <;> simp_all

/-- `ks`' IDs inserted, each `true`. -/
def promreg.insertAll (ks : List w64) (M : GMap w64 Bool) : GMap w64 Bool :=
  ks.foldl (fun m k => <[k := true]> m) M

theorem promreg.insertAll_lookup (ks : List w64) (M : GMap w64 Bool) (k : w64) :
    promreg.insertAll ks M !! k = if k ∈ ks then some true else M !! k := by
  induction ks generalizing M with
  | nil => rfl
  | cons a ks ih =>
    unfold promreg.insertAll at *
    rw [List.foldl_cons, ih]
    by_cases e : a = k
    · subst e; simp
    · rw [GMap.lookup_insert_ne _ _ e]; simp [Ne.symm e]

theorem promreg.insertAll_snoc (ks : List w64) (k : w64) (M : GMap w64 Bool) :
    promreg.insertAll (ks ++ [k]) M = <[k := true]> (promreg.insertAll ks M) := by
  unfold promreg.insertAll; rw [List.foldl_append]; rfl

section iris
variable [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {γ : GName}

/-- Every held right is absent from the registry's. -/
theorem promreg.regToks_absent_all (M : GMap w64 Bool) (ks : List w64) :
    ([∗map] k' ↦ _b ∈ M, promreg.idTok (GF := GF) γ k') ∗ promreg.idToks γ ks ⊢
      ⌜∀ k ∈ ks, M !! k = none⌝ ∗ ([∗map] k' ↦ _b ∈ M, promreg.idTok (GF := GF) γ k') ∗ promreg.idToks γ ks := by
  induction ks with
  | nil => iintro ⟨HM, Hk⟩; iframe; ipureintro; intro k hk; cases hk
  | cons a ks ih =>
    iintro ⟨HM, Hks⟩
    icases (promreg.idToks_cons (GF := GF) a ks).1 $$ Hks with ⟨Ha, Hks⟩
    icases promreg.regToks_absent (GF := GF) M a $$ [HM Ha] with ⟨%h1, HM, Ha⟩
    · iframe
    icases ih $$ [HM Hks] with ⟨%h2, HM, Hks⟩
    · iframe
    iframe HM
    isplitr
    · ipureintro
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact h1
      · exact h2 k hk
    iapply (promreg.idToks_cons (GF := GF) a ks).2
    iframe

/-- The held rights given to the registry. -/
theorem promreg.regToks_insertAll (M : GMap w64 Bool) (ks : List w64) :
    ([∗map] k' ↦ _b ∈ M, promreg.idTok (GF := GF) γ k') ∗ promreg.idToks γ ks ⊢
      [∗map] k' ↦ _b ∈ promreg.insertAll ks M, promreg.idTok (GF := GF) γ k' := by
  induction ks generalizing M with
  | nil => iintro ⟨HM, -⟩; simp only [promreg.insertAll, List.foldl_nil]; iexact HM
  | cons a ks ih =>
    iintro ⟨HM, Hks⟩
    icases (promreg.idToks_cons (GF := GF) a ks).1 $$ Hks with ⟨Ha, Hks⟩
    icases promreg.regToks_absent (GF := GF) M a $$ [HM Ha] with ⟨%h1, HM, Ha⟩
    · iframe
    ihave HM := promreg.regToks_insert (GF := GF) M a true h1 $$ [HM Ha]
    · iframe
    rw [show promreg.insertAll (a :: ks) M = promreg.insertAll ks (<[a := true]> M) from rfl]
    iapply (ih (<[a := true]> M))
    iframe

end iris

end helpers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : promreg.Assumptions]

theorem promreg.Registry.Register.wp_proof : promreg.Registry.Register.spec (GF := GF) (hG := hG) := by
  intro γ f r s dq ds Hok
  wp_start as ⟨#Hreg, Hs, Htoks⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold promreg.isRegistry at Hreg
  icases Hreg with ⟨%mI, %mD, %mC, #HI, #HD, #HC, #Hmu⟩
  wp_auto
  wp_apply wp_map_make1 (K := w64) (V := Bool) as %mS HmS
  wp_apply wp_map_make1 (K := GoString) (V := w64) as %mN HmN
  wp_apply (sync.Mutex.wp_Lock _ _) $$ [] as ⟨Hlk, HR⟩
  · iframe #
  iunfold promreg.regInv at HR
  icases HR with ⟨%ids, %dims, %cols, HmI, HmD, HmC, Hrt, %Hp⟩
  wp_auto
  obtain ⟨Hids, Hcols, Hdims⟩ := Hp
  obtain ⟨Hok1, Hok2, Hne⟩ := Hok
  icases promreg.regToks_absent_all (GF := GF) (ids ∪ cols) (promreg.descKeys ds) $$ [Hrt Htoks]
    with ⟨%Habs, Hrt, Htoks⟩
  · iframe
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  have hp0 : promreg.pIDs ds 0 = [] := by simp [promreg.pIDs]
  ihave Hinv : iprop(∃ (j : Nat) (sIDs : GoSlice) (seen : GMap w64 Bool) (sNm : GoSlice)
      (nd : GMap GoString w64) (nn : List GoString),
      "i" ∷ i_ptr ↦ W64 j ∗ "d" ∷ (∃ v : promreg.Desc, d_ptr ↦ v) ∗
      "newIDs" ∷ newIDs_ptr ↦ sIDs ∗ "SIDs" ∷ sIDs ↦* promreg.pIDs ds j ∗
      "CIDs" ∷ ownSliceCap w64 sIDs (DFrac.own 1) ∗
      "HmS" ∷ mS ↦$ seen ∗ "collectorID" ∷ collectorID_ptr ↦ promreg.xorAll (promreg.pIDs ds j) ∗
      "duplicate" ∷ duplicate_ptr ↦ false ∗ "HmN" ∷ mN ↦$ nd ∗
      "newNames" ∷ newNames_ptr ↦ sNm ∗ "SNm" ∷ sNm ↦* nn ∗ "CNm" ∷ ownSliceCap GoString sNm (DFrac.own 1) ∗
      "%Hj" ∷ ⌜j ≤ ds.length ∧ (∀ k, seen !! k = if k ∈ promreg.pIDs ds j then some true else none) ∧
        (∀ n h, nd !! n = some h → ∃ d ∈ ds, d.FQName' = n ∧ d.DimHash' = h) ∧
        (∀ n ∈ nn, ∃ d ∈ ds, d.FQName' = n)⌝)
      $$ [i d newIDs HmS collectorID duplicate HmN newNames]
  · iexists 0, slice.nil, ∅, slice.nil, ∅, []
    rw [hp0]
    iframe
    isplitl [d]
    · iexists _; iexact d
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro
    refine ⟨Nat.zero_le _, fun k => by simp, fun n h hn => by simp at hn, fun n hn => by cases hn⟩
  wp_for Hinv
  obtain ⟨Hj, Hseen, Hnd, Hnn⟩ := Hj
  by_cases hj : j < ds.length
  · have hc : sint.Z (W64 (j : Int)) < sint.Z s.len := by word
    simp only [decide_eq_true hc, ↓reduceIte]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨x, hx⟩ : ∃ x, ds[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    have hxm : x ∈ ds := List.mem_of_getElem? hx
    obtain ⟨hxv, hxid, hxb⟩ := Hok1 x hxm
    icases d with ⟨%v, d⟩
    wp_apply (wp_load_slice_index (t := promreg.Desc.ty) s (sint.Z (W64 (j : Int))) ds dq x h0) $$ [Hs] as Hs
    · iframe; ipureintro; rw [hsj]; exact hx
    have hxL : x.ID' ∈ promreg.pIDs ds ds.length :=
      (promreg.mem_pIDs ds ds.length x.ID').2 (by rw [List.take_length]; exact List.mem_map_of_mem hxm)
    have hxK : x.ID' ∈ promreg.descKeys ds := (promreg.mem_descKeys ds x.ID').2 (Or.inl hxL)
    have hxU := Habs x.ID' hxK
    have hxI : ids !! x.ID' = none := by
      rw [gmap_lookup_union] at hxU; cases h : ids !! x.ID' <;> simp_all
    rw [hxv]
    wp_auto
    wp_apply (wp_map_lookup1 go.uint64 go.bool mI ids x.ID') $$ [$HmI] as HmI
    rw [hxI, Option.getD_none, show zero_val Bool = false from rfl]
    wp_pures
    try wp_auto
    wp_apply (wp_map_lookup1 go.uint64 go.bool mS seen x.ID') $$ [$HmS] as HmS
    rw [Hseen x.ID']
    by_cases hs : x.ID' ∈ promreg.pIDs ds j
    · simp only [hs, ↓reduceIte, Option.getD_some]
      wp_pures
      try wp_auto
      have hL : promreg.pIDs ds (j + 1) = promreg.pIDs ds j := by
        rw [promreg.pIDs_succ ds j x hx, ite_eq_left_of_eq_true _ _ (eq_true hs)]
      have Hseen1 : ∀ k, seen !! k = if k ∈ promreg.pIDs ds (j + 1) then some true else none := by
        rw [hL]; exact Hseen
      rw [← hL]
      have hxD : dims !! x.FQName' = none := by
        cases h : dims !! x.FQName' with
        | none => rfl
        | some hh =>
          rcases Hdims _ _ h with h1 | h1
          · exact absurd h1 hxb
          · rw [← hxid, hxI] at h1; cases h1
      wp_apply (wp_map_lookup2 go.string go.uint64 mD dims x.FQName') $$ [$HmD] as HmD
      rw [hxD]
      simp only [Option.getD_none, Option.isSome_none]
      try wp_auto
      wp_apply (wp_map_lookup2 go.string go.uint64 mN nd x.FQName') $$ [$HmN] as HmN
      cases hn : nd !! x.FQName' with
      | some hh =>
        obtain ⟨d', hd', hd'n, hd'h⟩ := Hnd _ _ hn
        have hxh : x.DimHash' = hh := by rw [← hd'h]; exact Hok2 x hxm d' hd' hd'n.symm
        simp only [Option.getD_some, Option.isSome_some]
        try wp_auto
        rw [hxh]
        try wp_auto
        iapply wp_for_post_continue
        wp_auto
        iframe
        iexists (j + 1), _, _, sNm, nd, nn
        have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
        rw [hw]
        iframe
        isplitl [d]
        · iexists _; iexact d
        ipureintro
        exact ⟨hj, Hseen1, Hnd, Hnn⟩
      | none =>
        simp only [Option.getD_none, Option.isSome_none]
        try wp_auto
        wp_apply wp_mapInsert $$ [$HmN] as HmN
        wp_apply wp_slice_literal (l := [x.FQName'])
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨S, -⟩
        try wp_auto
        wp_apply wp_slice_append sNm nn _ [x.FQName'] (DFrac.own 1) $$ [$SNm $CNm $S]
          as %s3 ⟨SNm, CNm, -⟩
        try wp_auto
        iapply wp_for_post_do
        wp_auto
        iframe
        iexists (j + 1), _, _, s3, <[x.FQName' := x.DimHash']> nd, nn ++ [x.FQName']
        have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
        rw [hw]
        iframe
        isplitl [d]
        · iexists _; iexact d
        ipureintro
        refine ⟨hj, Hseen1, fun n h hnh => ?_, fun n hn' => ?_⟩
        · by_cases e : x.FQName' = n
          · subst e; rw [GMap.lookup_insert] at hnh; cases hnh; exact ⟨x, hxm, rfl, rfl⟩
          · rw [GMap.lookup_insert_ne _ _ e] at hnh; exact Hnd n h hnh
        · rcases List.mem_append.mp hn' with hn' | hn'
          · exact Hnn n hn'
          · rw [List.mem_singleton.mp hn']; exact ⟨x, hxm, rfl⟩
    · simp only [hs, ↓reduceIte, Option.getD_none]
      rw [show zero_val Bool = false from rfl]
      wp_pures
      try wp_auto
      wp_apply wp_mapInsert $$ [$HmS] as HmS
      wp_apply wp_slice_literal (l := [x.ID'])
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨S, -⟩
      try wp_auto
      wp_apply wp_slice_append sIDs (promreg.pIDs ds j) _ [x.ID'] (DFrac.own 1) $$ [$SIDs $CIDs $S]
        as %s2 ⟨SIDs, CIDs, -⟩
      try wp_auto
      have hL : promreg.pIDs ds (j + 1) = promreg.pIDs ds j ++ [x.ID'] := by
        rw [promreg.pIDs_succ ds j x hx, ite_eq_right_of_eq_false _ _ (eq_false hs)]
      have Hseen1 : ∀ k, (<[x.ID' := true]> seen) !! k =
          if k ∈ promreg.pIDs ds (j + 1) then some true else none := by
        intro k
        rw [hL]
        by_cases e : x.ID' = k
        · subst e; simp
        · rw [GMap.lookup_insert_ne _ _ e, Hseen k]
          simp [List.mem_append, Ne.symm e]
      rw [← promreg.xorAll_snoc, ← hL]
      have hxD : dims !! x.FQName' = none := by
        cases h : dims !! x.FQName' with
        | none => rfl
        | some hh =>
          rcases Hdims _ _ h with h1 | h1
          · exact absurd h1 hxb
          · rw [← hxid, hxI] at h1; cases h1
      wp_apply (wp_map_lookup2 go.string go.uint64 mD dims x.FQName') $$ [$HmD] as HmD
      rw [hxD]
      simp only [Option.getD_none, Option.isSome_none]
      try wp_auto
      wp_apply (wp_map_lookup2 go.string go.uint64 mN nd x.FQName') $$ [$HmN] as HmN
      cases hn : nd !! x.FQName' with
      | some hh =>
        obtain ⟨d', hd', hd'n, hd'h⟩ := Hnd _ _ hn
        have hxh : x.DimHash' = hh := by rw [← hd'h]; exact Hok2 x hxm d' hd' hd'n.symm
        simp only [Option.getD_some, Option.isSome_some]
        try wp_auto
        rw [hxh]
        try wp_auto
        iapply wp_for_post_continue
        wp_auto
        iframe
        iexists (j + 1), _, _, sNm, nd, nn
        have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
        rw [hw]
        iframe
        isplitl [d]
        · iexists _; iexact d
        ipureintro
        exact ⟨hj, Hseen1, Hnd, Hnn⟩
      | none =>
        simp only [Option.getD_none, Option.isSome_none]
        try wp_auto
        wp_apply wp_mapInsert $$ [$HmN] as HmN
        wp_apply wp_slice_literal (l := [x.FQName'])
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨S, -⟩
        try wp_auto
        wp_apply wp_slice_append sNm nn _ [x.FQName'] (DFrac.own 1) $$ [$SNm $CNm $S]
          as %s3 ⟨SNm, CNm, -⟩
        try wp_auto
        iapply wp_for_post_do
        wp_auto
        iframe
        iexists (j + 1), _, _, s3, <[x.FQName' := x.DimHash']> nd, nn ++ [x.FQName']
        have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
        rw [hw]
        iframe
        isplitl [d]
        · iexists _; iexact d
        ipureintro
        refine ⟨hj, Hseen1, fun n h hnh => ?_, fun n hn' => ?_⟩
        · by_cases e : x.FQName' = n
          · subst e; rw [GMap.lookup_insert] at hnh; cases hnh; exact ⟨x, hxm, rfl, rfl⟩
          · rw [GMap.lookup_insert_ne _ _ e] at hnh; exact Hnd n h hnh
        · rcases List.mem_append.mp hn' with hn' | hn'
          · exact Hnn n hn'
          · rw [List.mem_singleton.mp hn']; exact ⟨x, hxm, rfl⟩
  · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z s.len := by word
    simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    have hjl : j = ds.length := by omega
    subst hjl
    wp_auto
    ihave %HlenL := ownSlice_len _ _ _ $$ SIDs
    have hLne : promreg.pIDs ds ds.length ≠ [] := by
      obtain ⟨d0, hd0⟩ := List.exists_mem_of_ne_nil ds Hne
      intro h
      have := (promreg.mem_pIDs ds ds.length d0.ID').2 (by rw [List.take_length]; exact List.mem_map_of_mem hd0)
      rw [h] at this; cases this
    have hlen0 : sIDs.len ≠ W64 0 := by
      intro h
      apply hLne
      apply List.eq_nil_of_length_eq_zero
      rw [HlenL.1, h]; rfl
    simp only [hlen0, decide_false]
    wp_pures
    try wp_auto
    have hcK : promreg.xorAll (promreg.pIDs ds ds.length) ∈ promreg.descKeys ds :=
      (promreg.mem_descKeys ds _).2 (Or.inr rfl)
    obtain ⟨hcI, hcC⟩ := promreg.lookup_union_none ids cols _ (Habs _ hcK)
    wp_apply (wp_map_lookup1 go.uint64 go.bool mC cols _) $$ [$HmC] as HmC
    rw [hcC, Option.getD_none, show zero_val Bool = false from rfl]
    wp_pures
    try wp_auto
    wp_pures
    try wp_auto
    wp_apply wp_mapInsert $$ [$HmC] as HmC
    try wp_auto
    generalize hL : promreg.pIDs ds ds.length = L at *
    have hsL : sint.Z sIDs.len = (L.length : Int) := by have := HlenL.1; word
    ihave Hinv : iprop(∃ (k : Nat), "i" ∷ i_ptr ↦ W64 k ∗ "id" ∷ (∃ v : w64, id_ptr ↦ v) ∗
        "HmI" ∷ mI ↦$ promreg.insertAll (L.take k) ids ∗ "%Hk" ∷ ⌜k ≤ L.length⌝) $$ [i id HmI]
    · iexists 0
      iframe
      isplitl [id]
      · iexists _; iexact id
      ipureintro; exact Nat.zero_le _
    wp_for Hinv
    by_cases hk : k < L.length
    · have hc : sint.Z (W64 (k : Int)) < sint.Z sIDs.len := by rw [hsL]; word
      simp only [decide_eq_true hc, ↓reduceIte]
      wp_auto
      have h0 : 0 ≤ sint.Z (W64 (k : Int)) := by word
      simp only [h0, hc, and_self, ↓reduceIte]
      have hsk : (sint.Z (W64 (k : Int))).toNat = k := by word
      obtain ⟨x, hx⟩ : ∃ x, L[k]? = some x := ⟨_, List.getElem?_eq_getElem hk⟩
      icases id with ⟨%v, id⟩
      wp_apply (wp_load_slice_index (t := go.uint64) sIDs (sint.Z (W64 (k : Int))) L (DFrac.own 1) x h0) $$ [SIDs] as SIDs
      · iframe; ipureintro; rw [hsk]; exact hx
      wp_apply wp_mapInsert $$ [$HmI] as HmI
      iapply wp_for_post_do
      wp_auto
      iframe
      iexists (k + 1)
      have hw : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
      rw [hw]
      have htk : L.take (k + 1) = L.take k ++ [x] := by rw [List.take_add_one, hx]; rfl
      rw [htk, promreg.insertAll_snoc]
      iframe
      isplitl [id]
      · iexists _; iexact id
      ipureintro; exact hk
    · have hc : ¬ sint.Z (W64 (k : Int)) < sint.Z sIDs.len := by rw [hsL]; word
      simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
      have hkl : k = L.length := by omega
      subst hkl
      rw [List.take_length]
      wp_auto
      ihave %HlenN := ownSlice_len _ _ _ $$ SNm
      have hsN : sint.Z sNm.len = (nn.length : Int) := by have := HlenN.1; word
      have hIdsF : ∀ k, ids !! k = some true → promreg.insertAll L ids !! k = some true := by
        intro k hk; rw [promreg.insertAll_lookup]; split
        · rfl
        · exact hk
      have hLmem : ∀ d ∈ ds, promreg.insertAll L ids !! d.ID' = some true := by
        intro d hd
        rw [promreg.insertAll_lookup, ← hL]
        have : d.ID' ∈ promreg.pIDs ds ds.length :=
          (promreg.mem_pIDs ds ds.length d.ID').2 (by rw [List.take_length]; exact List.mem_map_of_mem hd)
        simp [this]
      ihave Hinv : iprop(∃ (k : Nat) (dims' : GMap GoString w64), "i" ∷ i_ptr ↦ W64 k ∗
          "n" ∷ (∃ v : GoString, n_ptr ↦ v) ∗ "HmD" ∷ mD ↦$ dims' ∗
          "%Hk" ∷ ⌜k ≤ nn.length ∧ ∀ n h, dims' !! n = some h →
            n ∈ promreg.builtinNames ∨ promreg.insertAll L ids !! f n = some true⌝) $$ [i n HmD]
      · iexists 0, dims
        iframe
        isplitl [n]
        · iexists _; iexact n
        ipureintro
        refine ⟨Nat.zero_le _, fun n h hn => ?_⟩
        rcases Hdims n h hn with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (hIdsF _ h1)
      wp_for Hinv
      obtain ⟨Hk, Hdims'⟩ := Hk
      by_cases hk : k < nn.length
      · have hc : sint.Z (W64 (k : Int)) < sint.Z sNm.len := by rw [hsN]; word
        simp only [decide_eq_true hc, ↓reduceIte]
        wp_auto
        have h0 : 0 ≤ sint.Z (W64 (k : Int)) := by word
        simp only [h0, hc, and_self, ↓reduceIte]
        have hsk : (sint.Z (W64 (k : Int))).toNat = k := by word
        obtain ⟨x, hx⟩ : ∃ x, nn[k]? = some x := ⟨_, List.getElem?_eq_getElem hk⟩
        icases n with ⟨%v, n⟩
        wp_apply (wp_load_slice_index (t := go.string) sNm (sint.Z (W64 (k : Int))) nn (DFrac.own 1) x h0) $$ [SNm] as SNm
        · iframe; ipureintro; rw [hsk]; exact hx
        wp_apply (wp_map_lookup1 go.string go.uint64 mN nd x) $$ [$HmN] as HmN
        wp_apply wp_mapInsert $$ [$HmD] as HmD
        iapply wp_for_post_do
        wp_auto
        iframe
        iexists (k + 1), _
        have hw : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
        rw [hw]
        iframe
        isplitl [n]
        · iexists _; iexact n
        ipureintro
        refine ⟨hk, fun n' h hn => ?_⟩
        by_cases e : x = n'
        · subst e
          obtain ⟨d, hd, hdn⟩ := Hnn x (List.mem_of_getElem? hx)
          right
          rw [← hdn, ← (Hok1 d hd).2.1]
          exact hLmem d hd
        · rw [GMap.lookup_insert_ne _ _ e] at hn; exact Hdims' n' h hn
      · have hc : ¬ sint.Z (W64 (k : Int)) < sint.Z sNm.len := by rw [hsN]; word
        simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
        wp_auto
        ihave Hrt := promreg.regToks_insertAll (GF := GF) (ids ∪ cols) (promreg.descKeys ds) $$ [Hrt Htoks]
        · iframe
        have hmap : promreg.insertAll (promreg.descKeys ds) (ids ∪ cols) =
            promreg.insertAll L ids ∪ <[promreg.xorAll L := true]> cols := by
          apply GMap.ext; intro k
          simp only [promreg.insertAll_lookup, gmap_lookup_union]
          have hm := promreg.mem_descKeys ds k
          rw [hL] at hm
          by_cases h1 : k ∈ L
          · rw [ite_eq_left_of_eq_true _ _ (eq_true (hm.2 (Or.inl h1))), ite_eq_left_of_eq_true _ _ (eq_true h1)]; rfl
          · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
            by_cases h2 : k = promreg.xorAll L
            · subst h2
              rw [ite_eq_left_of_eq_true _ _ (eq_true (hm.2 (Or.inr rfl))), GMap.lookup_insert, hcI]; rfl
            · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => (hm.1 h).elim h1 h2)),
                GMap.lookup_insert_ne _ _ (Ne.symm h2)]
        rw [hmap]
        wp_apply (sync.Mutex.wp_Unlock _ _) $$ [Hlk HmI HmD HmC Hrt]
        · iframe #
          iframe Hlk
          inext
          iunfold promreg.regInv
          iexists promreg.insertAll L ids, dims', <[promreg.xorAll L := true]> cols
          iframe
          ipureintro
          refine ⟨fun k b hk => ?_, fun k b hk => ?_, Hdims'⟩
          · rw [promreg.insertAll_lookup] at hk
            split at hk
            · cases hk; rfl
            · exact Hids k b hk
          · by_cases e : promreg.xorAll L = k
            · subst e; rw [GMap.lookup_insert] at hk; cases hk; rfl
            · rw [GMap.lookup_insert_ne _ _ e] at hk; exact Hcols k b hk
        simp only [promreg.OK]
        wp_auto
        iapply HΦ $$ Hs

end proof

end EtcdGrove
end Perennial
