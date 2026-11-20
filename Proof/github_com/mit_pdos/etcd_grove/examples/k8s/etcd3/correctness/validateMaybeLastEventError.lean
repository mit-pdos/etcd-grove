/-
Lean-first (no Rocq counterpart).

The proof of `validateMaybeLastEventError` on the accepting run: an Error event's view is a
`*metav1.Status` of status `Failure` at the last index (`lastErrOkL_at`), so no rejecting branch is
taken.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.validateMaybeLastEventError

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

/-- What `lastErrOkL` says of the event at index `j`. -/
theorem lastErrOkL_at {rs : List REv} (h : lastErrOkL rs = true) {j : Nat} {r : REv}
    (hr : rs[j]? = some r) (he : r.ty = evError) :
    r.o = .status go!"Failure" ∧ j + 1 = rs.length := by
  unfold lastErrOkL at h
  have hmem : (r, j) ∈ rs.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]; simpa using hr
  have := List.all_eq_true.1 h _ hmem
  simp only [he, ↓reduceIte] at this
  revert this
  cases r.o with
  | status s => intro h'; simp only [Bool.and_eq_true, decide_eq_true_eq] at h'; exact ⟨by rw [h'.1], h'.2⟩
  | _ => intro h'; cases h'

theorem validateMaybeLastEventError.wp_proof :
    validateMaybeLastEventError.spec (GF := GF) (hG := hG) := by
  intro sl rs hok
  wp_start as #Hs
  unfold evsRO
  icases Hs with ⟨%vs, #Hsl, #Hvs⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hvs
  wp_auto
  rename_i iv_ptr
  irename : (iv_ptr ↦ (zero_val w64) : IProp GF) => i0
  ihave HL : (∃ (j : w64) (ev : k8s_io.apimachinery.pkg.watch.Event) (iv : w64),
      "i" ∷ i_ptr ↦ j ∗ "ev" ∷ ev_ptr ↦ ev ∗ "i0" ∷ iv_ptr ↦ iv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len⌝ : IProp GF) $$ [i ev i0]
  · iexists W64 0, _, _
    iframe
    ipureintro; refine ⟨by word, by word⟩
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
    (try wp_auto)
    by_cases he : r.ty = evError
    · obtain ⟨hro, hlast⟩ := lastErrOkL_at hok hr he
      isimp only [hro] at Ho
      iunfold evObjRep at Ho
      icases Ho with ⟨%p, %st, ⟨%hob, %hst⟩, #Hp⟩
      have hev : v.Type' = go!"ERROR" := by rw [hty, he]; rfl
      simp only [hev, decide_true]
      wp_auto
      rw [hob]
      iStructNamed Hp
      wp_auto
      simp only [hst, decide_true, Bool.not_true]
      wp_auto
      have hjl : j = sl.len - W64 1 := by
        have : sint.nat j + 1 = sint.nat sl.len := by rw [hlast, ← Hl2, Hlen.1]
        word
      simp only [hjl, decide_true, Bool.not_true]
      wp_auto
      wp_for_post
      iframe
      iexists sl.len - W64 1 + W64 1, v, _
      iframe
      ipureintro; refine ⟨by word, by word⟩
    · have hev : v.Type' ≠ go!"ERROR" := by rw [hty]; exact he
      simp only [decide_eq_false hev]
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, v, _
      iframe
      ipureintro; refine ⟨by word, by word⟩
  · (try wp_auto)
    iapply HΦ; ipureintro; rfl

end proof

end k8s_correctness
end EtcdGrove
end Perennial
