/-
Lean-first (no Rocq counterpart).

The proof of `eventResourceVersionRange` when the pure function answers: the loop's state is
`evRangeR`'s fold (`evRangeStepR`) over the events visited, `some` on every prefix of a list it
answers on (`erFold_take_some`); each step's facts (`evRangeStepR_some`) rule out the error branches.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.eventResourceVersionRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.objectRV

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem erFold_none (l : List REv) : l.foldl evRangeStepR none = none := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simpa [List.foldl, evRangeStepR] using ih

theorem erFold_take_some {rs : List REv} {o : Option (w64 × w64)} (h : evRangeR rs = some o)
    (j : Nat) : ∃ acc, (rs.take j).foldl evRangeStepR (some (maxU64, 0)) = some acc := by
  unfold evRangeR at h
  rw [← List.take_append_drop j rs, List.foldl_append] at h
  cases hf : (rs.take j).foldl evRangeStepR (some (maxU64, 0)) with
  | none => rw [hf, erFold_none] at h; cases h
  | some acc => exact ⟨acc, rfl⟩

/-- What a step of `evRangeStepR` that does not fail says. -/
theorem evRangeStepR_some {mn mx : w64} {r : REv} {acc : w64 × w64}
    (h : evRangeStepR (some (mn, mx)) r = some acc) :
    (r.ty = evError → acc = (mn, mx)) ∧
    (r.ty ≠ evError → ∃ o, r.o = .obj o ∧
      ((r.ty = evAdded ∨ r.ty = evDeleted ∨ r.ty = evModified) →
        acc = (wmin mn o.ResourceVersion', wmax mx (o.ResourceVersion' + W64 1))) ∧
      (¬ (r.ty = evAdded ∨ r.ty = evDeleted ∨ r.ty = evModified) → r.ty = evBookmark ∧
        acc = (wmin mn (o.ResourceVersion' + W64 1), wmax mx o.ResourceVersion'))) := by
  unfold evRangeStepR at h
  by_cases he : r.ty = evError
  · simp only [he, ↓reduceIte, Option.some.injEq] at h
    exact ⟨fun _ => h.symm, fun h' => absurd he h'⟩
  refine ⟨fun h' => absurd h' he, fun _ => ?_⟩
  simp only [he, ↓reduceIte] at h
  cases ho : r.o with
  | status s => rw [ho] at h; cases h
  | other => rw [ho] at h; cases h
  | obj o =>
    rw [ho] at h
    simp only [objRVL] at h
    refine ⟨o, rfl, fun ha => ?_, fun ha => ?_⟩
    · simp only [ha, ↓reduceIte, Option.some.injEq] at h
      exact h.symm
    · simp only [ha, ↓reduceIte] at h
      by_cases hb : r.ty = evBookmark
      · simp only [hb, ↓reduceIte, Option.some.injEq] at h
        exact ⟨hb, h.symm⟩
      · simp only [hb, ↓reduceIte] at h; cases h

theorem eventResourceVersionRange.wp_proof
    (wp_objectRV : objectRV.spec (GF := GF) (hG := hG)) :
    eventResourceVersionRange.spec (GF := GF) (hG := hG) := by
  intro sl rs o hok
  have hmin : (#(functions go.min [go.uint64, go.uint64]) : val) = min.impl go.uint64 2 :=
    FuncUnfold.func_unfold (f := go.min) (type_args := List.replicate 2 go.uint64)
  have hmax : (#(functions go.max [go.uint64, go.uint64]) : val) = max.impl go.uint64 2 :=
    FuncUnfold.func_unfold (f := go.max) (type_args := List.replicate 2 go.uint64)
  wp_start as #Hs
  iunfold evsRO at Hs
  icases Hs with ⟨%vs, #Hsl, #Hvs⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hvs
  wp_auto
  ihave HL : (∃ (j : w64) (ev : k8s_io.apimachinery.pkg.watch.Event) (mn mx : w64),
      "i" ∷ i_ptr ↦ j ∗ "ev" ∷ ev_ptr ↦ ev ∗ "minRV" ∷ minRV_ptr ↦ mn ∗ "maxRV" ∷ maxRV_ptr ↦ mx ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧
        (rs.take (sint.nat j)).foldl evRangeStepR (some (maxU64, 0)) = some (mn, mx)⌝ : IProp GF)
      $$ [i ev minRV maxRV]
  · iexists W64 0, _, _, W64 0
    iframe
    ipureintro; refine ⟨by word, by word, rfl⟩
  wp_for HL
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem vs (sint.nat j) as v
    wp_apply (wp_load_slice_index sl (sint.Z j) vs DFrac.discard v Hj.1) $$ [Hsl] as -
    · isplit
      · iexact Hsl
      · ipureintro; exact Hv_lookup
    obtain ⟨r, hr⟩ : ∃ r, rs[sint.nat j]? = some r := by
      have : sint.nat j < rs.length := by rw [← Hl2]; word
      exact ⟨_, List.getElem?_eq_getElem this⟩
    ihave #Hv := BigSepL2.bigSepL2_lookup (Φ := fun _ v r => evRep (GF := GF) v r)
      Hv_lookup hr $$ Hvs
    ihave #Hv' := Hv
    iunfold evRep at Hv'
    icases Hv' with ⟨%hty, #Ho⟩
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have htake : rs.take (sint.nat j + 1) = rs.take (sint.nat j) ++ [r] := by
      rw [List.take_add_one, hr]; rfl
    obtain ⟨acc, hacc⟩ := erFold_take_some hok (sint.nat j + 1)
    rw [htake, List.foldl_append, Hj.2.2] at hacc
    simp only [List.foldl_cons, List.foldl_nil] at hacc
    obtain ⟨hE, hN⟩ := evRangeStepR_some hacc
    have hfold : ∀ acc', acc' = acc →
        (rs.take (sint.nat (j + W64 1))).foldl evRangeStepR (some (maxU64, 0)) = some acc' := by
      intro acc' h'
      rw [h', hj1, htake, List.foldl_append, Hj.2.2]
      simpa using hacc
    (try wp_auto)
    by_cases he : r.ty = evError
    · have hev : v.Type' = go!"ERROR" := by rw [hty, he]; rfl
      simp only [hev, decide_true]
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, v, mn, mx
      iframe
      ipureintro
      exact ⟨by word, by word, hfold _ (hE he).symm⟩
    · have hev : v.Type' ≠ go!"ERROR" := by rw [hty]; exact he
      simp only [decide_eq_false hev]
      (try wp_auto)
      obtain ⟨o, hro, hA, hB⟩ := hN he
      isimp only [hro] at Ho
      iunfold evObjRep at Ho
      wp_apply (wp_objectRV v.Object' o) $$ [Ho]
      · iframe #
      (try wp_auto)
      by_cases hA3 : r.ty = evAdded ∨ r.ty = evDeleted ∨ r.ty = evModified
      · have hacc' := hA hA3
        have hvT : v.Type' = go!"MODIFIED" ∨ v.Type' = go!"DELETED" ∨ v.Type' = go!"ADDED" := by
          rw [hty]; rcases hA3 with h | h | h <;> simp [h, evAdded, evDeleted, evModified]
        rcases hvT with hvT | hvT | hvT
        all_goals
          iterate 3
            ((try simp (config := { decide := true }) only [hvT]); (try wp_auto))
          iterate 4
            all_goals (try simp only [hmin, hmax])
            all_goals (try wp_auto)
            all_goals (try wp_if_destruct)
          all_goals
            wp_for_post
            iframe
            iexists j + W64 1, v, _, _
            iframe
            ipureintro
            refine ⟨by word, by word, hfold _ ?_⟩
            rw [hacc']; simp only [wmin, wmax, Prod.mk.injEq]
            constructor <;> split <;> word
      · obtain ⟨hb, hacc'⟩ := hB hA3
        have hvT : v.Type' = go!"BOOKMARK" := by rw [hty, hb]; rfl
        iterate 4
          ((try simp (config := { decide := true }) only [hvT]); (try wp_auto))
        iterate 4
          all_goals (try simp only [hmin, hmax])
          all_goals (try wp_auto)
          all_goals (try wp_if_destruct)
        all_goals
          wp_for_post
          iframe
          iexists j + W64 1, v, _, _
          iframe
          ipureintro
          refine ⟨by word, by word, hfold _ ?_⟩
          rw [hacc']; simp only [wmin, wmax, Prod.mk.injEq]
          constructor <;> split <;> word
  · have hfull : rs.take (sint.nat j) = rs := List.take_of_length_le (by rw [← Hl2]; word)
    rw [hfull] at Hj
    have ho : evRangeR rs = (if mn = maxU64 ∨ mx = 0 then some none else some (some (mn, mx))) := by
      unfold evRangeR; rw [Hj.2.2]
    rw [hok] at ho
    (try wp_auto)
    have hM : maxU64 = W64 18446744073709551615 := rfl
    by_cases h1 : mn = W64 18446744073709551615
    · have hc : mn = maxU64 ∨ mx = 0 := Or.inl (by rw [h1]; rfl)
      simp only [hc, ↓reduceIte, Option.some.injEq] at ho
      subst ho
      simp only [h1, decide_true]
      (try wp_auto)
      iapply HΦ
      unfold rangeRep
      ipureintro; exact ⟨rfl, rfl⟩
    simp only [decide_eq_false h1]
    (try wp_auto)
    by_cases h2 : mx = W64 0
    · have hc : mn = maxU64 ∨ mx = 0 := Or.inr h2
      simp only [hc, ↓reduceIte, Option.some.injEq] at ho
      subst ho
      simp only [h2, decide_true]
      (try wp_auto)
      iapply HΦ
      unfold rangeRep
      ipureintro; exact ⟨rfl, rfl⟩
    · have hc : ¬ (mn = maxU64 ∨ mx = 0) := by
        rintro (h | h)
        · exact h1 (by rw [h]; rfl)
        · exact h2 h
      simp only [hc, ↓reduceIte, Option.some.injEq] at ho
      subst ho
      simp only [decide_eq_false h2]
      (try wp_auto)
      iapply HΦ
      isplitr
      · ipureintro; rfl
      unfold rangeRep
      iframe

end proof

end k8s_correctness
end EtcdGrove
end Perennial
