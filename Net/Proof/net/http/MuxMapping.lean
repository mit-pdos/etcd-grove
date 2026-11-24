/-
net/http's `mapping[string, *routingNode]` (`mapping.go`), the children of a node of the ServeMux's
routing tree: a slice of entries while it has few (`maxSlice`), then a Go map.

* `MapSt`: its physical state (the two fields, the slice's entries, the map's contents).
* `mapRep dq h st kids`: the mapping at `h` holds the pairs `kids` (distinct keys), at fraction
  `dq`; the slice's entries are never written again once appended (`↦*□`), and the map is owned
  at `dq`. Fixed `st`, so it is fractional (`mapRep_fractional`), for the ServeMux's `RWMutex`.
* `wp_mapping_find`, `wp_mapping_add`: `find` and `add` (a key not yet in `kids`).
-/
module

public import Net.GeneratedProof.net.http

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section st
variable [GooseExts]

/-- The physical state of a `mapping[string, *routingNode]` (see the file header). -/
structure MapSt where
  s : GoSlice
  m : GoMap
  es : List (net.http.entry GoString Loc)
  M : GMap GoString Loc

/-- The pairs of a list of entries. -/
def entPairs (es : List (net.http.entry GoString Loc)) : List (GoString × Loc) :=
  es.map (fun e => (e.key', e.value'))

/-- The type of the routing tree's children. -/
abbrev kidsTy [GoGlobalContext] : go.GoType :=
  net.http.mapping.ty go.string (go.GoType.PointerType net.http.routingNode.ty)

theorem lookupL_entPairs_found (k : GoString) : ∀ (es : List (net.http.entry GoString Loc))
    (i : Nat) (x : net.http.entry GoString Loc), es[i]? = some x → x.key' = k →
    (∀ j (y : net.http.entry GoString Loc), j < i → es[j]? = some y → y.key' ≠ k) →
    map.lookupL k (entPairs es) = some x.value'
  | [], _, _, hx, _, _ => by simp at hx
  | e :: es, 0, x, hx, hk, _ => by
    simp at hx; subst hx; simp [entPairs, map.lookupL, hk]
  | e :: es, i + 1, x, hx, hk, hpre => by
    have he : e.key' ≠ k := hpre 0 e (by omega) rfl
    have := lookupL_entPairs_found k es i x (by simpa using hx) hk
      (fun j y hj hy => hpre (j + 1) y (by omega) (by simpa using hy))
    simp only [entPairs, List.map_cons, map.lookupL] at this ⊢
    rw [ite_eq_right_iff.mpr (fun h => absurd h.symm he)]; exact this

theorem lookupL_entPairs_none (k : GoString) : ∀ (es : List (net.http.entry GoString Loc)),
    (∀ (j : Nat) (y : net.http.entry GoString Loc), es[j]? = some y → y.key' ≠ k) → map.lookupL k (entPairs es) = none
  | [], _ => rfl
  | e :: es, h => by
    have he : e.key' ≠ k := h 0 e rfl
    simp only [entPairs, List.map_cons, map.lookupL]
    rw [ite_eq_right_iff.mpr (fun h => absurd h.symm he)]
    exact lookupL_entPairs_none k es (fun j y hy => h (j + 1) y (by simpa using hy))

end st

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]

/-- The mapping at `h` holds `kids` (see the file header). -/
def mapRep (dq : DFrac) (h : Loc) (st : MapSt) (kids : List (GoString × Loc)) : IProp GF :=
  iprop(structFieldRef (net.http.mapping GoString Loc) go!"s" h ↦{dq} st.s ∗
    structFieldRef (net.http.mapping GoString Loc) go!"m" h ↦{dq} st.m ∗
    ⌜(kids.map Prod.fst).Nodup⌝ ∗
    (if st.m = map.nil then
      st.s ↦*□ st.es ∗ ownSliceCap (net.http.entry GoString Loc) st.s dq ∗ ⌜entPairs st.es = kids⌝
    else st.m ↦${dq} st.M ∗ ⌜∀ k, st.M !! k = map.lookupL k kids⌝))

/-- `h.find(k)` (see the file header). -/
theorem wp_mapping_find (h : Loc) (dq : DFrac) (st : MapSt) (kids : List (GoString × Loc))
    (k : GoString) (hnn : h ≠ null) :
    {{ mapRep (GF := GF) (hG := hG) dq h st kids }}
      (App (Val (h @!! go.GoType.PointerType kidsTy @!! go!"find")) (Val #k))
    {{ RET (PairV #((map.lookupL k kids).getD null) #(decide ((map.lookupL k kids).isSome)));
        mapRep dq h st kids }} := by
  by_cases hm : st.m = map.nil
  · simp only [mapRep, hm, ↓reduceIte]
    wp_start as ⟨Hs, Hm, %Hnd, #Hes, Hcap, %Hkids⟩
    wp_auto
    rw [decide_eq_false hnn]
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ Hes
    ihave HI : (∃ (i : w64) (ev : net.http.entry GoString Loc), "i" ∷ i_ptr ↦ i ∗
        "e" ∷ e_ptr ↦ ev ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z st.s.len ∧
          ∀ j x, j < sint.nat i → st.es[j]? = some x → x.key' ≠ k⌝ : IProp GF) $$ [i e]
    · iexists W64 0, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro j x hj; exact absurd hj (by word)
    wp_for HI
    wp_if_destruct
    · simp only [Hi.1, Hif, _root_.and_self, ↓reduceIte]
      list_elem st.es (sint.nat i) as x
      wp_apply wp_load_slice_index st.s (sint.Z i) st.es _ x (by word) $$ [Hes] with Hes
      · iframe #; ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word]; exact Hx_lookup
      wp_if_destruct
      · wp_for_post
        have hl := lookupL_entPairs_found _ st.es (sint.nat i) x Hx_lookup rfl Hi.2.2
        rw [Hkids] at hl
        rw [hl]
        simp only [Option.getD_some, Option.isSome_some, decide_true]
        iapply HΦ
        iframe; iframe #; ipureintro; exact ⟨Hnd, Hkids⟩
      · wp_for_post
        iframe
        iexists i + W64 1, x
        iframe
        ipureintro
        refine ⟨by word, by word, fun j y hj hy => ?_⟩
        by_cases hji : j < sint.nat i
        · exact Hi.2.2 j y hji hy
        · have : j = sint.nat i := by word
          subst this; rw [Hx_lookup] at hy; cases hy; assumption
    · have hnone : map.lookupL k kids = none := by
        rw [← Hkids]; apply lookupL_entPairs_none
        intro j y hy
        have hj : j < st.es.length := by
          rcases (List.getElem?_eq_some_iff.mp hy) with ⟨hj, _⟩; exact hj
        exact Hi.2.2 j y (by word) hy
      rw [hnone]
      simp only [Option.getD_none, Option.isSome_none, Bool.false_eq_true, decide_false]
      rw [show (null : Loc) = zero_val Loc from rfl]
      iapply HΦ
      iframe; iframe #; ipureintro; exact ⟨Hnd, Hkids⟩
  · simp only [mapRep, hm, ↓reduceIte]
    wp_start as ⟨Hs, Hm, %Hnd, HM, %HMk⟩
    wp_auto
    rw [decide_eq_false hnn]
    wp_auto
    rw [decide_eq_false hm]
    wp_auto
    wp_apply wp_map_lookup2 go.string (go.GoType.PointerType net.http.routingNode.ty) st.m st.M k dq $$ HM with HM
    rw [HMk k, show (zero_val Loc) = null from rfl]
    iapply HΦ
    iframe
    ipureintro; exact ⟨Hnd, HMk⟩

end defs

end net.http
end Perennial
