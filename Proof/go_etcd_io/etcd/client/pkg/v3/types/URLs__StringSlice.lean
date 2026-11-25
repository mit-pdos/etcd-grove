/-
The proof of `(*types.URLs).StringSlice`: goose's pointer-method wrapper (load `*p`, call the value
method), then `make([]string, len(us))` and `out[i] = us[i].String()` for each URL, over
`url.URL.String`'s spec (`http.URLStringAny_spec`; the loop as `rafthttp.setPeerURLsHeader`'s).
Until 2026-11-21 a trust-boundary axiom. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.URLs__StringSlice

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.types.Assumptions]

theorem types.URLs.StringSlice.wp_proof
    (hURLString : http.URLStringAny_spec (GF := GF)) :
    types.URLs.StringSlice.spec (GF := GF) (hG := hG) := by
  intro p dq sl us
  wp_start as ⟨Hp, #Hus⟩
  ihave %Hul := ownSlice_len _ _ _ $$ Hus
  wp_auto
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply wp_slice_make2 (V := GoString) as %out ⟨Hout, Houtcap⟩
  · ipureintro; exact Hul.2
  (try wp_auto)
  -- `for i := range us { out[i] = us[i].String() }`
  rename_i iu_ptr
  irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
  ihave HF : (∃ (k iv : w64) (xs : List GoString),
      "i" ∷ i_ptr ↦ k ∗ "Hiu" ∷ iu_ptr ↦ iv ∗ "Hout" ∷ out ↦* xs ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z sl.len ∧ xs.length = us.length ∧
        ∀ (j : Nat) (u : _root_.Perennial.net.url.URL), j < sint.nat k → us[j]? = some u →
          http.urlRootPlain u → xs[j]? = some (go!"http://" ++ u.Host')⌝ : IProp GF)
    $$ [i Hiu Hout]
  · iexists W64 0, _, _
    iframe
    ipureintro
    refine ⟨by decide, Hul.2, by rw [List.length_replicate, Hul.1], fun j u hj _ _ => ?_⟩
    exact absurd hj (by simp)
  wp_for HF
  obtain ⟨Hk1, Hk2, Hk3, Hk4⟩ := Hk
  (try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false])
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := ⟨Hk1, Hif⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    list_elem us (sint.nat k) as u
    -- the range's element, loaded (unused: the body indexes `us` again)
    wp_apply (wp_load_slice_index sl (sint.Z k) us DFrac.discard u Hk1) $$ [] as -
    · iframe #; ipureintro; exact Hu_lookup
    (try wp_auto)
    (try simp only [Hb, _root_.and_self, ↓reduceIte])
    ihave ⟨Hu, -⟩ := (ownSlice_elem_acc (sint.Z k) u sl DFrac.discard us Hk1 Hu_lookup) $$ Hus
    wp_apply (hURLString _ DFrac.discard u) $$ [Hu] as %s ⟨-, %Hs⟩
    · iexact Hu
    (try wp_auto)
    ihave %Houtl := ownSlice_len $$ Hout
    have Hb' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z out.len := by
      constructor
      · exact Hk1
      · have : xs.length = us.length := Hk3
        word
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [Hout] as Hout
    · iframe; ipureintro; constructor <;> word
    wp_for_post
    iframe
    iexists k + W64 1, k, _
    iframe
    ipureintro
    refine ⟨by word, by word, by simp [Hk3], fun j v hj hv hvr => ?_⟩
    have hkn : sint.nat (k + W64 1) = sint.nat k + 1 := by unfold sint.nat; word
    rw [hkn] at hj
    rw [List.getElem?_set]
    by_cases hjk : sint.nat k = j
    · subst hjk
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl),
        ite_eq_left_of_eq_true _ _ (eq_true (by rw [Hk3]; exact (List.getElem?_eq_some_iff.1 hv).1))]
      have : v = u := by rw [hv] at Hu_lookup; exact Option.some.inj Hu_lookup
      subst this
      rw [Hs hvr]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hjk)]
      exact Hk4 j v (by omega) hv hvr
  · (try wp_auto)
    iapply HΦ
    iframe
    ipureintro
    refine ⟨Hk3, fun j u hu hur => Hk4 j u ?_ hu hur⟩
    have hjl : j < us.length := (List.getElem?_eq_some_iff.1 hu).1
    have := Hul.1
    unfold sint.nat at *; word

/-- `StringSlice` of plain URLs (claim #34, stage 2, 2026-11-25): the same loop, its invariant also
saying the strings written so far are `http://` and each URL's host. -/
theorem types.URLs.StringSlice.wp_proofP
    (hURLString : http.URLStringAny_spec (GF := GF)) :
    types.URLs.StringSlice.specP (GF := GF) (hG := hG) := by
  intro p dq sl us Hplain
  wp_start as ⟨Hp, #Hus⟩
  ihave %Hul := ownSlice_len _ _ _ $$ Hus
  wp_auto
  wp_method_call
  wp_call
  (try wp_auto)
  wp_apply wp_slice_make2 (V := GoString) as %out ⟨Hout, Houtcap⟩
  · ipureintro; exact Hul.2
  (try wp_auto)
  rename_i iu_ptr
  irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
  ihave HF : (∃ (k iv : w64) (xs : List GoString),
      "i" ∷ i_ptr ↦ k ∗ "Hiu" ∷ iu_ptr ↦ iv ∗ "Hout" ∷ out ↦* xs ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z sl.len ∧ xs.length = us.length ∧
        ∀ j, j < sint.nat k → xs[j]? = (us.map fun u => go!"http://" ++ u.Host')[j]?⌝ :
        IProp GF)
    $$ [i Hiu Hout]
  · iexists W64 0, _, _
    iframe
    ipureintro
    refine ⟨by decide, Hul.2, by rw [List.length_replicate, Hul.1], ?_⟩
    intro j hj
    exact absurd hj (by simp)
  wp_for HF
  obtain ⟨Hk1, Hk2, Hk3, Hk4⟩ := Hk
  (try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false])
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := ⟨Hk1, Hif⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    list_elem us (sint.nat k) as u
    wp_apply (wp_load_slice_index sl (sint.Z k) us DFrac.discard u Hk1) $$ [] as -
    · iframe #; ipureintro; exact Hu_lookup
    (try wp_auto)
    (try simp only [Hb, _root_.and_self, ↓reduceIte])
    ihave ⟨Hu, -⟩ := (ownSlice_elem_acc (sint.Z k) u sl DFrac.discard us Hk1 Hu_lookup) $$ Hus
    wp_apply (hURLString _ DFrac.discard u) $$ [Hu] as %s ⟨-, %Hs⟩
    · iexact Hu
    (try wp_auto)
    ihave %Houtl := ownSlice_len $$ Hout
    have Hb' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z out.len := by
      constructor
      · exact Hk1
      · have : xs.length = us.length := Hk3
        word
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [Hout] as Hout
    · iframe; ipureintro; constructor <;> word
    have hsu : s = go!"http://" ++ u.Host' :=
      Hs (Hplain u (List.mem_of_getElem? Hu_lookup))
    wp_for_post
    iframe
    iexists k + W64 1, k, _
    iframe
    ipureintro
    have hn : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    refine ⟨by word, by word, by simp [Hk3], ?_⟩
    intro j hj
    rw [hn] at hj
    have hkl : sint.nat k < xs.length := by rw [Hk3, Hul.1]; word
    by_cases hjk : j = sint.nat k
    · subst hjk
      rw [List.getElem?_set_self hkl, List.getElem?_map, Hu_lookup, hsu]
      rfl
    · rw [List.getElem?_set_ne (Ne.symm hjk)]
      exact Hk4 j (by omega)
  · (try wp_auto)
    iapply HΦ
    iframe
    have hk : sint.nat k = us.length := by rw [Hul.1]; word
    have hxs : xs = us.map fun u => go!"http://" ++ u.Host' := by
      apply List.ext_getElem?
      intro j
      by_cases hj : j < us.length
      · exact Hk4 j (by omega)
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
    rw [← hxs]
    iexact Hout

end proof

end EtcdGrove
end Perennial
