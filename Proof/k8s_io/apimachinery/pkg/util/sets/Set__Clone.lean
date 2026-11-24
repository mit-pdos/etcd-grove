/-
`Set[T].Clone()` (`set.go`): a copy. Lean-first; for the union builder's `ToDecision`. Its proof
(unfinished). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Clone
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods
public import Proof.k8s_io.apimachinery.pkg.util.sets.CloneB1

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apimachinery.pkg.util.sets

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]

/-- `Clone` inserts the keys one by one; its statement has no callee hypothesis, so it uses the copy
of `Set.Insert`'s proof in `CloneB1.lean`. -/
theorem Set.Clone.wp_proof :
    Set.Clone.spec (GF := GF) (hG := hG) := by
  intro K _ _ _ _ T _ _ m dq s
  wp_start as Hm
  wp_auto
  wp_apply wp_map_len $$ Hm as Hm
  rw [go.make2_underlying, (go.is_underlying : underlying (Set''.ty T) = _)]
  wp_apply (wp_map_make2 (K := K) (V := Elem) _ T Empty.ty) as %r Hr
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List K) (p : Int) => iprop(∃ (x : K),
      "%Hp" ∷ ⌜0 ≤ p⌝ ∗
      "key" ∷ key_ptr ↦ x ∗ "result" ∷ result_ptr ↦ r ∗
      "Hr" ∷ r ↦$ insertAll ∅ (keys.take p.toNat))) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [key result Hr]
  · iexists _
    simp only [named]
    iframe
    ipureintro; exact Int.le_refl _
  isplitr
  · imodintro
    iintro %p %k %o ⟨%Hkey, %Ho⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply (Set.wp_ptr_Insert_of Set.wp_Insert_b1) $$ [$result $Hr $Hl1] as ⟨result, Hr, -⟩
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists k
    simp only [named]
    have Htake : keys.take (p + 1).toNat = keys.take p.toNat ++ [k] := by
      rw [show (p + 1).toNat = p.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    rw [Htake, insertAll_append]
    iframe
    ipureintro; omega
  · iintro HP Hm
    iNamed HP
    rw [← Hklen, Int.toNat_natCast, List.take_length, insertAll_keys_b1 s keys Hkset, keysOf_set_b1]
    wp_auto
    iapply HΦ
    iframe

end proof

end sets
end EtcdGrove
end Perennial
