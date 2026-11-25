/-
net/http's Go 1.22 registration (`ServeMux.registerErr`'s steps) on literal path patterns
(`litPat`, `MuxTree.lean`).

* `routingIndexKey_safe`: the index's struct key compares by value (`go_eq_struct` over its two
  fields, `int` and `string`), so it is a safe map key.
* `wp_mapping_add`: `mapping.add` of a key not yet among the children.
-/
module

public import Net.Proof.net.http.MuxTree

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]

instance routingIndexKey.decEq : DecidableEq net.http.routingIndexKey := fun a b =>
  decidable_of_iff (a.pos' = b.pos' ∧ a.s' = b.s') (by cases a; cases b; simp)

instance routingIndexKey_safe (k : net.http.routingIndexKey) :
    SafeMapKey (GF := GF) (keys := mapKeys_all _) net.http.routingIndexKey.ty k where
  key_ok := trivial
  wp_go_eq_map_key k' _ s E Φ := by
    iintro HΦ
    wp_auto
    by_cases hp : k.pos' = k'.pos'
    · rw [decide_eq_true hp]
      wp_auto
      have : decide (k = k') = decide (k.s' = k'.s') := by
        cases k; cases k'; simp at hp ⊢; simp [hp]
      rw [this]
      iapply HΦ
    · rw [decide_eq_false hp]
      wp_auto
      have : decide (k = k') = false := decide_eq_false (fun h => hp (by rw [h]))
      rw [this]
      iapply HΦ

theorem lookupL_append_one {K V : Type} [DecidableEq K] (k k' : K) (v : V) :
    ∀ ps : List (K × V), map.lookupL k' (ps ++ [(k, v)]) =
      (match map.lookupL k' ps with | some x => some x | none => if k' = k then some v else none)
  | [] => by simp [map.lookupL]
  | p :: ps => by
    simp only [List.cons_append, map.lookupL]
    by_cases h : k' = p.1
    · simp [h]
    · simp only [h, ↓reduceIte]; exact lookupL_append_one k k' v ps

theorem kids_append_nodup (kids : List (GoString × Loc)) (k : GoString) (v : Loc)
    (hnd : (kids.map Prod.fst).Nodup) (hk : map.lookupL k kids = none) :
    ((kids ++ [(k, v)]).map Prod.fst).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨hnd, by simp, ?_⟩
  intro a ha b hb; simp at hb; subst hb
  intro hab; subst hab
  exact (map.lookupL_eq_none_iff _ _).mp hk ha

theorem entPairs_take_succ (es : List (net.http.entry GoString Loc)) (i : Nat)
    (x : net.http.entry GoString Loc) (hx : es[i]? = some x) :
    entPairs (es.take (i + 1)) = entPairs (es.take i) ++ [(x.key', x.value')] := by
  have hi : i < es.length := (List.getElem?_eq_some_iff.mp hx).1
  rw [List.take_add_one, hx]; simp [entPairs]

theorem key_not_in_take (es : List (net.http.entry GoString Loc)) (i : Nat)
    (x : net.http.entry GoString Loc) (hx : es[i]? = some x)
    (hnd : ((entPairs es).map Prod.fst).Nodup) :
    map.lookupL x.key' (entPairs (es.take i)) = none := by
  rw [map.lookupL_eq_none_iff]
  have hi : i < es.length := (List.getElem?_eq_some_iff.mp hx).1
  have hsplit : es = es.take i ++ x :: es.drop (i + 1) := by
    conv => lhs; rw [← List.take_append_drop i es]
    rw [List.drop_eq_getElem_cons hi]
    rw [List.getElem?_eq_getElem hi] at hx; cases hx; rfl
  rw [hsplit] at hnd
  simp only [entPairs, List.map_append, List.map_cons, List.map_map] at hnd
  have := (List.nodup_append.mp hnd).2.2
  intro hm
  simp only [entPairs, List.map_map] at hm
  exact this _ hm _ (by simp) rfl

theorem lookup_step (es : List (net.http.entry GoString Loc)) (i : Nat)
    (x : net.http.entry GoString Loc) (hx : es[i]? = some x)
    (hnd : ((entPairs es).map Prod.fst).Nodup) (Mi : GMap GoString Loc)
    (hMi : ∀ k', Mi !! k' = map.lookupL k' (entPairs (es.take i))) :
    ∀ k', (GMap.insert x.key' x.value' Mi) !! k' = map.lookupL k' (entPairs (es.take (i + 1))) := by
  intro k'
  rw [entPairs_take_succ es i x hx, lookupL_append_one, GMap.lookup_insert_eq_iff]
  by_cases hk : x.key' = k'
  · subst hk; simp [key_not_in_take es i x hx hnd]
  · simp only [hk, ↓reduceIte, hMi k']
    cases map.lookupL k' (entPairs (es.take i)) <;> simp [Ne.symm hk]

/-- `h.add(k, v)` of a key not among the children (the owner, at `1`). -/
theorem wp_mapping_add (h : Loc) (st : MapSt) (kids : List (GoString × Loc)) (k : GoString)
    (v : Loc) (ms : w64) (hk : map.lookupL k kids = none) :
    {{ globalAddr net.http.maxSlice ↦□ ms ∗ mapRep (GF := GF) (hG := hG) (DFrac.own 1) h st kids }}
      (App (App (Val (h @!! go.GoType.PointerType kidsTy @!! go!"add")) (Val #k)) (Val #v))
    {{ RET #(); ∃ st' : MapSt, mapRep (DFrac.own 1) h st' (kids ++ [(k, v)]) }} := by
  by_cases hm : st.m = map.nil
  · simp only [mapRep, hm, ↓reduceIte]
    wp_start as ⟨#Hms, Hh, %Hnd, #Hes, Hcap, %Hkids⟩
    ihave %hnn := typedPointsto_not_null _ _ _ $$ Hh
    iStructNamedPrefix Hh "H"
    wp_auto
    wp_if_destruct
    · wp_apply (wp_slice_literal (l := [({ key' := k, value' := v } : net.http.entry GoString Loc)]))
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      try wp_auto
      wp_apply (wp_slice_append_persistent (V := net.http.entry GoString Loc) st.s st.es _
        [({ key' := k, value' := v } : net.http.entry GoString Loc)] (DFrac.own 1))
        $$ [$Hes $Hcap $Hsl] as %s' ⟨#Hes', Hcap', -⟩
      try wp_auto
      iapply HΦ
      iexists { s := s', m := map.nil, es := st.es ++ [{ key' := k, value' := v }], M := st.M }
      simp only [↓reduceIte]
      ihave Hh := typedPointsto_combine h ({ s' := s', m' := map.nil } : net.http.mapping GoString Loc) (DFrac.own 1) hnn $$ [Hs Hm]
      · simp only [TypedPointsto.typedPointstoDef]; iframe
      iframe; iframe #
      ipureintro
      refine ⟨kids_append_nodup kids k v Hnd hk, ?_⟩
      simp [entPairs, ← Hkids]
    · wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string _) as %m' HM
      try wp_auto
      ihave %Hlen := ownSlice_len _ _ _ $$ Hes
      ihave HI : (∃ (i : w64) (ev : net.http.entry GoString Loc) (Mi : GMap GoString Loc),
          "i" ∷ i_ptr ↦ i ∗ "e" ∷ e_ptr ↦ ev ∗ "HM" ∷ m' ↦$ Mi ∗
          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z st.s.len ∧
            ∀ k', Mi !! k' = map.lookupL k' (entPairs (st.es.take (sint.nat i)))⌝ : IProp GF)
          $$ [i e HM]
      · iexists W64 0, _, _
        iframe
        ipureintro
        refine ⟨by word, by word, fun k' => ?_⟩
        rw [show sint.nat (W64 0) = 0 by word]
        simp [entPairs, map.lookupL]
      wp_for HI
      wp_if_destruct
      · try wp_auto
        simp only [Hi.1, Hif, _root_.and_self, ↓reduceIte]
        list_elem st.es (sint.nat i) as x
        wp_apply wp_load_slice_index st.s (sint.Z i) st.es _ x (by word) $$ [Hes] with Hes
        · iframe #; ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word]; exact Hx_lookup
        try wp_auto
        wp_apply (wp_mapInsert (K := GoString) (V := Loc) go.string m' Mi x.key' x.value') $$ HM as HM
        try wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, x, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
        exact lookup_step st.es (sint.nat i) x Hx_lookup (by rw [Hkids]; exact Hnd) Mi Hi.2.2
      · have hall : sint.nat i = st.es.length := by word
        wp_apply (wp_mapInsert (K := GoString) (V := Loc) go.string m' Mi k v) $$ HM as HM
        try wp_auto
        ihave %hm'n := ownMap_not_nil _ _ _ $$ HM
        iapply HΦ
        iexists { s := slice.nil, m := m', es := [], M := GMap.insert k v Mi }
        simp only [hm'n, ↓reduceIte]
        ihave Hh := typedPointsto_combine h ({ s' := slice.nil, m' := m' } : net.http.mapping GoString Loc) (DFrac.own 1) hnn $$ [Hs Hm]
        · simp only [TypedPointsto.typedPointstoDef]; iframe
        iframe
        ipureintro
        refine ⟨kids_append_nodup kids k v Hnd hk, fun k' => ?_⟩
        rw [GMap.lookup_insert_eq_iff, lookupL_append_one]
        have hMi := Hi.2.2 k'
        rw [hall, List.take_length, Hkids] at hMi
        by_cases hk' : k = k'
        · subst hk'; simp [hk]
        · simp only [hk', ↓reduceIte, hMi]
          cases map.lookupL k' kids <;> simp [Ne.symm hk']
  · simp only [mapRep, hm, ↓reduceIte]
    wp_start as ⟨#Hms, Hh, %Hnd, HM, %HMk⟩
    ihave %hnn := typedPointsto_not_null _ _ _ $$ Hh
    iStructNamedPrefix Hh "H"
    wp_auto
    rw [decide_eq_false hm]
    wp_auto
    rw [decide_eq_false hm]
    wp_auto
    wp_apply (wp_mapInsert (K := GoString) (V := Loc) go.string st.m st.M k v) $$ HM as HM
    try wp_auto
    iapply HΦ
    iexists { s := st.s, m := st.m, es := st.es, M := GMap.insert k v st.M }
    simp only [hm, ↓reduceIte]
    ihave Hh := typedPointsto_combine h ({ s' := st.s, m' := st.m } : net.http.mapping GoString Loc) (DFrac.own 1) hnn $$ [Hs Hm]
    · simp only [TypedPointsto.typedPointstoDef]; iframe
    iframe
    ipureintro
    refine ⟨kids_append_nodup kids k v Hnd hk, fun k' => ?_⟩
    rw [GMap.lookup_insert_eq_iff, lookupL_append_one, HMk k']
    by_cases hk' : k = k'
    · subst hk'; simp [hk]
    · simp only [hk', ↓reduceIte]
      cases map.lookupL k' kids <;> simp [Ne.symm hk']

end wp

end net.http
end Perennial
