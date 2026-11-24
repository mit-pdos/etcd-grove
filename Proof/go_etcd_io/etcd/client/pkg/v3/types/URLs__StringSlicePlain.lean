/-
The proof of `(*types.URLs).StringSlice`'s variant with the URL strings (`URLs__StringSlicePlain.lean`), as
`URLs__StringSlice.lean`'s: goose's pointer-method wrapper (load `*p`, call the value
method), then `make([]string, len(us))` and `out[i] = us[i].String()` for each URL, over
`url.URL.String`'s spec (`http.URLStringAny_spec`; the loop as `rafthttp.setPeerURLsHeader`'s).
Until 2026-11-21 a trust-boundary axiom. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.URLs__StringSlicePlain

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

theorem types.URLs.StringSlicePlain.wp_proof
    (hURLString : http.URLStringAny_spec (GF := GF)) :
    types.URLs.StringSlicePlain.spec (GF := GF) (hG := hG) := by
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
        ∀ (i : Nat) (u : _root_.Perennial.net.url.URL), i < sint.nat k → us[i]? = some u →
          http.urlRootPlain u → xs[i]? = some (go!"http://" ++ u.Host')⌝ : IProp GF)
    $$ [i Hiu Hout]
  · iexists W64 0, _, _
    iframe
    ipureintro
    exact ⟨by decide, Hul.2, by rw [List.length_replicate, Hul.1],
      fun i u hi => absurd hi (by simp)⟩
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
    refine ⟨by word, by word, by simp [Hk3], ?_⟩
    intro i u' hi hu' hp
    have hkn : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    rw [hkn] at hi
    rw [List.getElem?_set]
    by_cases hik : i = sint.nat k
    · subst hik
      rw [hu'] at Hu_lookup
      cases Hu_lookup
      have hlt : sint.nat k < xs.length := by rw [Hk3]; exact (List.getElem?_eq_some_iff.1 hu').1
      simp only [hlt, if_true, Option.some.injEq]
      exact Hs hp
    · rw [if_neg (Ne.symm (by intro h; exact hik (by word)))]
      exact Hk4 i u' (by omega) hu' hp
  · (try wp_auto)
    iapply HΦ
    iframe
    ipureintro
    refine ⟨Hk3, fun i u hu hp => Hk4 i u ?_ hu hp⟩
    have := (List.getElem?_eq_some_iff.1 hu).1
    word

end proof

end EtcdGrove
end Perennial
