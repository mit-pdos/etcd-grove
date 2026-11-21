/-
Proof of `apierrors.StatusCause` (`Spec/k8s_io/apimachinery/pkg/api/errors/StatusCause.lean`) over its
body (prove-k8s2, 2026-11-20).
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.StatusCause
public import Proof.k8s_io.apimachinery.pkg.api.errors.Checks

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

theorem StatusCause.wp_proof
    (wp_AsNoMatch : errors.AsNoMatch.spec (GF := GF) (hG := hG)) :
    StatusCause.spec (GF := GF) (hG := hG) := by
  intro err name
  wp_start as #Hok
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Hc := apiErrOk_cases err $$ Hok
  icases Hc with (⟨%st, %cs, #Hst⟩ | #Hpl)
  · ihave #Hag := apiErrAt_status_agree err st cs $$ Hst
    iunfold apiErrAt at Hst
    icases Hst with ⟨%l, %hl, #Hl, #Hd⟩
    subst hl
    wp_auto
    simp only [statusErrorPtr_apiStatus, ↓reduceIte]
    wp_auto
    ihave Hl' := Hl
    iStructNamed Hl'
    iStructNamed ErrStatus
    wp_method_call
    wp_auto
    iunfold statusDetailsAt at Hd
    icases Hd with (%hd | ⟨%d, #Hdp, #Hcs⟩)
    · obtain ⟨hdn, rfl⟩ := hd
      simp only [hdn, _root_.decide_true, Bool.not_true]
      wp_auto
      iapply HΦ
      iintro !> %w #Hw
      ihave %hw := Hag $$ Hw
      subst hw
      ipureintro
      simp [causeIn]
    · icases typedPointsto_not_null _ _ _ $$ Hdp with %hnn
      rw [decide_eq_false hnn]
      wp_auto
      wp_method_call
      wp_auto
      ihave Hdp' := Hdp
      iStructNamed Hdp'
      wp_auto
      ihave %Hlen := ownSlice_len _ _ _ $$ Hcs
      ihave HI : (∃ (j : w64) (c0 : k8s_io.apimachinery.pkg.apis.«meta».v1.StatusCause),
          "i" ∷ i_ptr ↦ j ∗ "cause" ∷ cause_ptr ↦ c0 ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z d.Causes'.len ∧
            name ∉ (cs.take (sint.nat j)).map (·.Type')⌝ : IProp GF) $$ [i cause]
      · iexists W64 0, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        intro h
        have h0 : sint.nat (W64 0) = 0 := by word
        rw [h0] at h
        simp at h
      wp_for HI
      by_cases hlt : sint.Z j < sint.Z d.Causes'.len
      · simp only [hlt, _root_.decide_true, ↓reduceIte]
        wp_auto
        simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z d.Causes'.len from ⟨Hj.1, hlt⟩,
          _root_.and_self, ↓reduceIte]
        list_elem cs (sint.nat j) as c
        wp_apply (wp_load_slice_index d.Causes' (sint.Z j) cs DFrac.discard c Hj.1) $$ []
        · iframe Hcs
          ipureintro
          exact Hc_lookup
        iintro -
        wp_auto
        by_cases hty : c.Type' = name
        · simp only [hty, _root_.decide_true]
          wp_auto
          wp_for_post
          iapply HΦ
          iintro !> %w #Hw
          ihave %hw := Hag $$ Hw
          subst hw
          ipureintro
          simp only [causeIn, List.mem_map]
          exact (decide_eq_true ⟨c, List.mem_of_getElem? Hc_lookup, hty⟩).symm
        · simp only [hty, _root_.decide_false]
          wp_auto
          wp_for_post
          iframe
          iexists j + W64 1, c
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hc_lookup]
          simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
            List.mem_append, List.mem_singleton, not_or]
          exact ⟨Hj.2.2, fun h => hty h.symm⟩
      · simp only [hlt, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
        wp_auto
        iapply HΦ
        iintro !> %w #Hw
        ihave %hw := Hag $$ Hw
        subst hw
        ipureintro
        have hj : sint.nat j = cs.length := by rw [Hlen.1]; word
        rw [hj, List.take_length] at Hj
        simp only [causeIn]
        exact (decide_eq_false Hj.2.2).symm
  · ihave #Hag := apiErrAt_plain_agree err $$ Hpl
    ihave %hsh := apiErrAt_plain_shape err $$ Hpl
    rcases hsh with rfl | ⟨ii, rfl, hts⟩
    all_goals
      wp_auto
      try simp only [hts, Bool.false_eq_true, ↓reduceIte]
      try wp_auto
      wp_apply (wp_As_plain wp_AsNoMatch _ _ _) $$ [status]
      · iframe
        try iexact Hpl
      iintro status
      wp_auto
      iapply HΦ
      iintro !> %w #Hw
      ihave %hw := Hag $$ Hw
      subst hw
      ipureintro
      rfl

end proof

end apierrors
end EtcdGrove
end Perennial
