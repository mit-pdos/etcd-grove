/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/ValidateListOptions.lean`. Lean-first (no Rocq
counterpart): no continue token, so the paging branch is skipped; an empty resource version returns
`0`; else the versioner's parse (`versionerOk`), then the match's case.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.ValidateListOptions

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode k8s

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

set_option hygiene false in
/-- The remaining steps after the versioner's parse, and the answer. -/
local macro "vlo_tail" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h <;> rw [h] <;> (try wp_auto) <;> (try rw [hr]) <;> (try wp_auto) <;>
  (repeat' (wp_if_destruct <;> (try wp_auto))) <;>
  (simp only [listRevL]; (try simp_all); (try (rw [if_neg (by omega)])); (try (rw [if_pos (by omega)]));
    iapply HΦ; itrivial)))

theorem storage.ValidateListOptions.wp_proof :
    storage.ValidateListOptions.spec (GF := GF) (hG := hG) := by
  intro Obj S kp vi opts n hc hp hm
  wp_start as Hver
  iunfold versionerOk at Hver
  icases Hver with ⟨-, -, -, #HParse⟩
  (try wp_auto)
  cases hr : opts.Recursive' <;> (try wp_auto)
  · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %hlen
    by_cases hrv : opts.ResourceVersion' = []
    · have hn : n = W64 0 := Option.some.inj (hp.symm.trans (hrv ▸ S.parse_empty))
      subst hn
      rw [decide_eq_true (by rw [hrv]; rfl)]
      (try wp_auto)
      simp only [listRevL]; (try simp); iapply HΦ; itrivial
    · rw [decide_eq_false (by
        intro h; apply hrv; apply List.eq_nil_of_length_eq_zero
        have := congrArg BitVec.toNat h; simp at this; omega)]
      (try wp_auto)
      wp_bind
      iapply HParse
      inext
      iintro %n' %err' %hn'
      rw [hp] at hn'
      obtain ⟨rfl, rfl⟩ := hn'
      (try wp_auto)
      vlo_tail
  · rw [hc]
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    (try wp_auto)
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %hlen
    by_cases hrv : opts.ResourceVersion' = []
    · have hn : n = W64 0 := Option.some.inj (hp.symm.trans (hrv ▸ S.parse_empty))
      subst hn
      rw [decide_eq_true (by rw [hrv]; rfl)]
      (try wp_auto)
      simp only [listRevL]; (try simp); iapply HΦ; itrivial
    · rw [decide_eq_false (by
        intro h; apply hrv; apply List.eq_nil_of_length_eq_zero
        have := congrArg BitVec.toNat h; simp at this; omega)]
      (try wp_auto)
      wp_bind
      iapply HParse
      inext
      iintro %n' %err' %hn'
      rw [hp] at hn'
      obtain ⟨rfl, rfl⟩ := hn'
      (try wp_auto)
      vlo_tail

end proof

end EtcdGrove
end Perennial
