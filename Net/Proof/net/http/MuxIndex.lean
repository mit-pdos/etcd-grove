/-
net/http's Go 1.22 routing index (`routing_index.go`, the `ServeMux`'s `index`) on literal path
patterns (`litPat`, `MuxTree.lean`): only the registering owner touches it (`registerErr`, under
the mux's lock held for writing), so it is owned outright, not shared through the lock.

* `pidx R pp`: a `*pattern` in the index, of a literal pattern among the registered `R`
  (persistent); `slIdx R sl`: a slice of them (persistent: the index's slices are only appended
  to); `idxRep ix R`: the index at `ix` (its `segments` map, every value such a slice with its
  capacity, and its `multis`). `idxRep_mono`: registering more patterns keeps it.
* `wp_index_addPattern`: `idx.addPattern(pat)` of a literal pattern: the index of `p :: R`.
* `wp_possiblyConflictingPatterns_lit`: over a callback `f` that returns `nil` for every pattern
  of the index (`noConflictFn`), `idx.possiblyConflictingPatterns(pat, f)` returns `nil`.
-/
module

public import Net.Proof.net.http.MuxConflict

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section inj
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [package_sem' : net.http.Assumptions]

/-- A field read is deterministic, so equal struct values have equal fields. -/
private theorem field_eq {S T : Type} (op : GoInstruction)
    (proj : S → T) (hg : ∀ z : S, is_go_step_pure op #z = Eq (Val #(proj z))) {x y : S}
    (h : (#x : val) = #y) : (#(proj x) : val) = #(proj y) := by
  have e := hg x
  rw [h, hg y] at e
  have h2 : (Val #(proj y) : Expr) = Val #(proj x) := (congrFun e (Val #(proj x))).mpr rfl
  injection h2.symm

/-- A `routingIndexKey` value determines its fields (the index's map keys). -/
instance routingIndexKey.intoValInj [go.BasicIntoValInj] : go.IntoValInj net.http.routingIndexKey where
  intoVal_inj x y h := by
    have h1 := go.intoVal_inj (field_eq _ _ (fun z =>
      (net.http.routingIndexKey.TypeAssumptions.get_pos z).isGoStep_det_internal.isGoStep_pure_det) h)
    have h2 := go.intoVal_inj (field_eq _ _ (fun z =>
      (net.http.routingIndexKey.TypeAssumptions.get_s z).isGoStep_det_internal.isGoStep_pure_det) h)
    cases x; cases y
    simp only at h1 h2
    subst h1 h2; rfl

end inj

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]

/-- A `*pattern` in the index: a registered literal pattern among `R` (persistent). -/
def pidx (R : List (List w8)) (pp : Loc) : IProp GF :=
  iprop(∃ q : List w8, patRep pp q ∗ ⌜litPat q ∧ q ∈ R⌝)

instance pidx_persistent (R : List (List w8)) (pp : Loc) :
    Persistent (pidx (GF := GF) (hG := hG) R pp) := by
  unfold pidx; infer_instance

/-- A slice of the index's patterns (persistent). -/
def slIdx (R : List (List w8)) (sl : GoSlice) : IProp GF :=
  iprop(∃ ps : List Loc, sl ↦*□ ps ∗ [∗list] pp ∈ ps, pidx R pp)

instance slIdx_persistent (R : List (List w8)) (sl : GoSlice) :
    Persistent (slIdx (GF := GF) (hG := hG) R sl) := by
  unfold slIdx; infer_instance

/-- The index at `ix`, its patterns among `R` (owned by the registering owner). -/
def idxRep (ix : Loc) (R : List (List w8)) : IProp GF :=
  iprop(∃ (m : GoMap) (M : GMap net.http.routingIndexKey GoSlice) (msl : GoSlice),
    structFieldRef net.http.routingIndex go!"segments" ix ↦ m ∗
    (if m = map.nil then ⌜M = ∅⌝ else m ↦$ M) ∗
    □ ([∗map] _k ↦ sl ∈ M, slIdx R sl) ∗
    ([∗map] _k ↦ sl ∈ M, ownSliceCap Loc sl (DFrac.own 1)) ∗
    structFieldRef net.http.routingIndex go!"multis" ix ↦ msl ∗
    slIdx R msl ∗ ownSliceCap Loc msl (DFrac.own 1))

theorem pidx_mono (R R' : List (List w8)) (h : ∀ q ∈ R, q ∈ R') (pp : Loc) :
    pidx (GF := GF) (hG := hG) R pp ⊢ pidx R' pp := by
  unfold pidx
  iintro ⟨%q, #Hq, %hq⟩
  iexists q
  iframe #
  ipureintro; exact ⟨hq.1, h q hq.2⟩

theorem slIdx_mono (R R' : List (List w8)) (h : ∀ q ∈ R, q ∈ R') (sl : GoSlice) :
    slIdx (GF := GF) (hG := hG) R sl ⊢ slIdx R' sl := by
  unfold slIdx
  iintro ⟨%ps, #Hsl, #Hps⟩
  iexists ps
  iframe #
  iapply BigSepL.bigSepL_mono (fun _ => pidx_mono R R' h _) $$ Hps

theorem slIdx_nil (R : List (List w8)) : ⊢ slIdx (GF := GF) (hG := hG) R slice.nil := by
  unfold slIdx
  iexists ([] : List Loc)
  isplitl []
  · iapply (ownSlice_nil (V := Loc) (GF := GF) DFrac.discard)
  iapply BigSepL.bigSepL_nil_intro (P := iprop(True))
  ipureintro; trivial

theorem idxRep_mono (ix : Loc) (R R' : List (List w8)) (h : ∀ q ∈ R, q ∈ R') :
    idxRep (GF := GF) (hG := hG) ix R ⊢ idxRep ix R' := by
  unfold idxRep
  iintro ⟨%m, %M, %msl, Hm, HM, #HP, Hcaps, Hms, #Hmsl, Hmcap⟩
  iexists m, M, msl
  iframe
  isplitl []
  · imodintro
    iapply BigSepM.bigSepM_mono (fun _ => slIdx_mono R R' h _) $$ HP
  iapply slIdx_mono R R' h $$ Hmsl

/-- A registered `*pattern` of `p`, now among `p :: R`. -/
theorem pidx_new (R : List (List w8)) (pp : Loc) (p : List w8) (hp : litPat p) :
    patRep (GF := GF) (hG := hG) pp p ⊢ pidx (p :: R) pp := by
  unfold pidx
  iintro #H
  iexists p
  iframe #
  ipureintro; exact ⟨hp, List.mem_cons_self⟩

/-- Appending `pp` to a slice of the index. -/
theorem slIdx_snoc (R : List (List w8)) (sl sl' : GoSlice) (ps : List Loc) (pp : Loc) :
    sl ↦*□ ps ∗ ([∗list] x ∈ ps, pidx (GF := GF) (hG := hG) R x) ∗ sl' ↦*□ (ps ++ [pp]) ∗
      pidx R pp ⊢ slIdx R sl' := by
  unfold slIdx
  iintro ⟨-, #Hps, #Hsl', #Hpp⟩
  iexists ps ++ [pp]
  isplitl []
  · iexact Hsl'
  iapply BigSepL.bigSepL_snoc.2
  isplitl []
  · iexact Hps
  iexact Hpp

/-- A key's slice in the index (`nil` for none), its capacity, and the map back with a new one. -/
theorem idx_take (R : List (List w8)) (M : GMap net.http.routingIndexKey GoSlice)
    (k : net.http.routingIndexKey) :
    (□ ([∗map] _k ↦ x ∈ M, slIdx (GF := GF) (hG := hG) R x)) ∗
      ([∗map] _k ↦ x ∈ M, ownSliceCap Loc x (DFrac.own 1)) ⊢
      slIdx R ((M !! k).getD (zero_val GoSlice)) ∗
      ownSliceCap Loc ((M !! k).getD (zero_val GoSlice)) (DFrac.own 1) ∗
      (∀ v', ownSliceCap Loc v' (DFrac.own 1) -∗
        [∗map] _k ↦ x ∈ insert M k v', ownSliceCap (GF := GF) Loc x (DFrac.own 1)) := by
  iintro ⟨#HP, Hc⟩
  cases h : M !! k with
  | none =>
    simp only [Option.getD_none, show (zero_val GoSlice) = slice.nil from rfl]
    isplitl []
    · iapply slIdx_nil
    isplitl []
    · iapply ownSliceCap_nil
    iintro %v' Hv
    iapply (BigSepM.bigSepM_insert h).2
    iframe
  | some old =>
    simp only [Option.getD_some]
    isplitl []
    · iapply BigSepM.bigSepM_lookup h $$ HP
    iapply BigSepM.bigSepM_insert_acc h $$ Hc

/-- The index's slices with a key's new one. -/
theorem idx_put (R : List (List w8)) (M : GMap net.http.routingIndexKey GoSlice)
    (k : net.http.routingIndexKey) (v' : GoSlice) :
    (□ ([∗map] _k ↦ x ∈ M, slIdx (GF := GF) (hG := hG) R x)) ∗ slIdx R v' ⊢
      □ ([∗map] _k ↦ x ∈ insert M k v', slIdx R x) := by
  iintro ⟨#HP, #Hv⟩
  imodintro
  iapply (BigSepM.bigSepM_insert_elim (Φ := fun _ x => slIdx (GF := GF) (hG := hG) R x)) $$ Hv HP

end defs

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]

set_option hygiene false in
/-- `wp_index_addPattern`'s loop over the segments, the index's map at `mt` (not `nil`). -/
local macro "idx_loop " mt:term:max : tactic => `(tactic| (
  ihave %hm'n := ownMap_not_nil _ _ _ $$ HM
  ihave HI : (∃ (i : w64) (sv : net.http.segment) (pv : w64)
      (M' : GMap net.http.routingIndexKey GoSlice),
      "i" ∷ i_ptr ↦ i ∗ "seg" ∷ seg_ptr ↦ sv ∗ "pos" ∷ pos_ptr ↦ pv ∗ "HM" ∷ $mt ↦$ M' ∗
      "HP" ∷ □ ([∗map] _k ↦ x ∈ M', slIdx (GF := GF) (hG := hG) (p :: R) x) ∗
      "Hcaps" ∷ ([∗map] _k ↦ x ∈ M', ownSliceCap Loc x (DFrac.own 1)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i⌝ : IProp GF) $$ [i seg pos HM Hcaps]
  · iexists W64 0, _, _, _
    iframe
    isplitl []
    · iframe #
    ipureintro; word
  wp_for HI
  icases HP with #HP
  wp_if_destruct
  · try wp_auto
    simp only [Hi, Hif, _root_.and_self, ↓reduceIte]
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    list_elem (List.map segVal (pathSegs p)) (sint.nat i) as x
    wp_apply wp_load_slice_index sl (sint.Z i) _ _ x (by word) $$ [Hsl] as _Hsl2
    · iframe #; ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word]; exact Hx_lookup
    obtain ⟨y, hy, rfl⟩ : ∃ y, (pathSegs p)[sint.nat i]? = some y ∧ x = segVal y := by
      rw [List.getElem?_map] at Hx_lookup
      cases h : (pathSegs p)[sint.nat i]? with
      | none => rw [h] at Hx_lookup; simp at Hx_lookup
      | some y => rw [h] at Hx_lookup; exact ⟨y, rfl, (Option.some.inj Hx_lookup).symm⟩
    obtain ⟨t, rfl⟩ : ∃ t, y = .lit t := by
      cases y with
      | lit t => exact ⟨t, rfl⟩
      | multi =>
        exfalso
        have hl := multi_at_last p hp _ hy
        rw [List.getLast?_eq_getElem?, hl, Nat.add_sub_cancel, hy] at hx
        cases hx
    simp only [segVal]
    try wp_auto
    simp only
    ihave Htk := idx_take (p :: R) M' ⟨i, t⟩ $$ [HP Hcaps]
    · iframe; iframe #
    icases Htk with ⟨#Hold, Hcold, Hclose⟩
    wp_apply (wp_map_lookup1 (K := net.http.routingIndexKey) (V := GoSlice) _ _ $mt M' _
      (DFrac.own 1)) $$ HM as HM
    wp_apply (wp_slice_literal (l := [pp]))
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hlit, -⟩
    try wp_auto
    ihave #Hold' := Hold
    iunfold slIdx at Hold'
    icases Hold' with ⟨%ps, #Hps, #Hpsi⟩
    wp_apply (wp_slice_append_persistent (V := Loc) _ ps _ [pp] (DFrac.own 1))
      $$ [Hps Hcold Hlit] as %s' ⟨#Hs', Hcap', -⟩
    · iframe; iframe #
    try wp_auto
    wp_apply (wp_mapInsert (K := net.http.routingIndexKey) (V := GoSlice) _ $mt M' _ s') $$ HM as HM
    try wp_auto
    ihave #Hnsl := slIdx_snoc (p :: R) _ s' ps pp $$ [Hps Hpsi Hs' Hnew]
    · iframe #
    ihave #HP' := idx_put (p :: R) M' ⟨i, t⟩ s' $$ [HP Hnsl]
    · iframe #
    ihave Hcaps' := Hclose $$ Hcap'
    wp_for_post
    iframe
    iexists i + W64 1, _, _, _
    iframe
    isplitl []
    · iframe #
    ipureintro; word
  · try wp_auto
    iapply HΦ
    iunfold idxRep
    iexists $mt, M', msl
    simp only [hm'n, ↓reduceIte]
    iframe
    iframe #))

/-- `idx.addPattern(pat)` of a literal pattern `p`: the index of `p :: R`. -/
theorem wp_index_addPattern (ix pp : Loc) (R : List (List w8)) (p : List w8) (hp : litPat p) :
    {{ idxRep (GF := GF) (hG := hG) ix R ∗ patRep pp p }}
      (App (Val (ix @!! go.GoType.PointerType net.http.routingIndex.ty @!! go!"addPattern")) (Val #pp))
    {{ RET #(); idxRep ix (p :: R) }} := by
  wp_start as ⟨Hix, #Hpr⟩
  ihave Hix := idxRep_mono ix R (p :: R) (fun q hq => List.mem_cons_of_mem _ hq) $$ Hix
  ihave #Hnew := pidx_new R pp p hp $$ Hpr
  iunfold idxRep at Hix
  icases Hix with ⟨%m, %M, %msl, Hm, HM, #HP, Hcaps, Hms, #Hmsl, Hmcap⟩
  ihave #Hpr' := Hpr
  iunfold patRep at Hpr'
  icases Hpr' with ⟨%sl, %loc, #Hpp, #Hsl⟩
  wp_auto
  obtain ⟨x, hx⟩ : ∃ x, (pathSegs p).getLast? = some x := by
    cases h : (pathSegs p).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) (pathSegs_ne_nil p hp)
    | some x => exact ⟨x, rfl⟩
  wp_apply wp_lastSegment pp p x hx $$ [$Hpr]
  cases x with
  | multi =>
    simp only [segVal]
    wp_auto
    wp_apply (wp_slice_literal (l := [pp]))
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hlit, -⟩
    try wp_auto
    iunfold slIdx at Hmsl
    icases Hmsl with ⟨%ps, #Hps, #Hpsi⟩
    wp_apply (wp_slice_append_persistent (V := Loc) msl ps _ [pp] (DFrac.own 1))
      $$ [$Hps $Hmcap $Hlit] as %s' ⟨#Hs', Hcap', -⟩
    try wp_auto
    iapply HΦ
    iunfold idxRep
    iexists m, M, s'
    iframe
    iframe #
    iapply slIdx_snoc (p :: R) msl s' ps pp
    iframe #
  | lit s =>
    simp only [segVal]
    wp_auto
    iStructNamedPrefix Hpp "P"
    by_cases hm : m = map.nil
    · irevert HM; simp only [hm, ↓reduceIte]; iintro %HM0
      subst HM0
      wp_auto
      wp_apply (wp_map_make1 (K := net.http.routingIndexKey) (V := GoSlice) _ _) as %m' HM
      try wp_auto
      idx_loop m'
    · irevert HM; simp only [hm, ↓reduceIte]; iintro HM
      wp_auto
      idx_loop m

end wp

end net.http
end Perennial
