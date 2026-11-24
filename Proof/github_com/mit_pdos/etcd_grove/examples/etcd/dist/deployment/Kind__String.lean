/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/deployment/Kind__String.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Kind__String
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.kindNames

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

theorem deployment.Kind.String.wp_proof (hNames : etcd_dist.deployment.kindNames.spec (GF := GF) (hG := hG)) :
    etcd_dist.deployment.Kind.String.spec (GF := GF) (hG := hG) := by
  intro k
  by_cases hk : kindKnown k
  · rw [show kindName k = kindNameList.getD (sint.nat k) [] from if_pos hk]
    obtain ⟨hk0, hk1⟩ := hk
    wp_start
    wp_auto
    wp_if_destruct
    · exfalso; word
    · wp_apply hNames as %sl Hsl
      ihave %Hl := ownSlice_len _ _ _ $$ Hsl
      have h11 : kindNameList.length = 11 := rfl
      wp_if_destruct
      · exfalso; word
      · wp_apply hNames as %sl2 Hsl2
        ihave %Hl2 := ownSlice_len _ _ _ $$ Hsl2
        have hlt : sint.nat k < kindNameList.length := by rw [h11]; word
        obtain ⟨x, hx⟩ : ∃ x, kindNameList[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem hlt⟩
        have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl2.len := ⟨hk0, by word⟩
        simp only [hb, and_self, ↓reduceIte]
        wp_apply (wp_load_slice_index sl2 (sint.Z k) kindNameList (DFrac.own 1) x hk0) $$ [Hsl2] as Hsl2
        · iframe; ipureintro; rw [show (sint.Z k).toNat = sint.nat k by word]; exact hx
        rw [show kindNameList.getD (sint.nat k) [] = x by rw [List.getD_eq_getElem?_getD, hx]; rfl]
        wp_end
  · rw [show kindName k = go!"unknown" from if_neg hk]
    unfold kindKnown at hk
    wp_start
    wp_auto
    wp_if_destruct
    · wp_end
    · wp_apply hNames as %sl Hsl
      ihave %Hl := ownSlice_len _ _ _ $$ Hsl
      have h11 : kindNameList.length = 11 := rfl
      wp_if_destruct
      · wp_end
      · exfalso; apply hk; constructor <;> word
end proof

end etcd_dist
end EtcdGrove
end Perennial
