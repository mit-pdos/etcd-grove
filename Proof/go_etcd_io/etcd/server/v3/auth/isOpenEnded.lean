/-
`isOpenEnded`'s proof (the auth plan's S2, 2026-10-23); see `InvAuth.lean`, `PermTree.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.isOpenEnded
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.isOpenEnded.wp_proof :
    auth.isOpenEnded.spec (GF := GF) (hG := hG) := by
  intro re e de
  wp_start as He
  ihave %Hl := ownSlice_len _ _ _ $$ He
  wp_auto
  wp_if_destruct
  · have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z re.len := by
      rw [Hif]; decide
    have hlen : e.length = 1 := by rw [Hl.1, Hif]; rfl
    obtain ⟨x, hx⟩ : ∃ x, e[0]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have he : e = [x] := by
      match e, hlen, hx with
      | [y], _, h => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; rw [h]
    simp only [Hbnd, and_self, ite_true]
    wp_apply wp_load_slice_index re (sint.Z (W64 0)) e de x (by decide) $$ [He] as He
    · iframe He; ipureintro; exact hx
    have heq : decide (auth.isOpenEnded e) = decide (x = W8 0) := by
      subst he; unfold auth.isOpenEnded; simp
    rw [heq]
    wp_end
  · have hne : e.length ≠ 1 := by
      intro h; apply Hif; rw [Hl.1] at h; have := Hl.2; word
    have heq : decide (auth.isOpenEnded e) = false := by
      apply decide_eq_false; intro h; apply hne; rw [h]; rfl
    rw [heq]
    wp_end

end proof

end EtcdGrove
end Perennial
