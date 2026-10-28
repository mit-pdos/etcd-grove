/-
Proof of `Spec/k8s_io/apimachinery/pkg/util/sets/Set__UnsortedList.lean`. Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__UnsortedList

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.sets

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]

theorem Set.UnsortedList.wp_proof : Set.UnsortedList.spec (GF := GF) (hG := hG) := by
  intro K _ _ _ _ T _ m dq s
  wp_start as Hm
  (try wp_auto)
  wp_apply wp_map_len_lt $$ Hm as ⟨Hm, %Hsz⟩
  wp_apply (wp_slice_make3 (V := K) (W64 0) (W64 (GMap.size s)) (by word)) as %sl0 ⟨Hsl0, Hcap0, -⟩
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List K) (p : Int) => iprop(∃ (x : K) (sl : GoSlice),
      "%Hp" ∷ ⌜0 ≤ p⌝ ∗
      "key" ∷ key_ptr ↦ x ∗ "res" ∷ res_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* keys.take p.toNat ∗ "Hcap" ∷ ownSliceCap K sl (DFrac.own 1))) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [key res Hsl0 Hcap0]
  · iexists _, sl0
    simp only [named]
    simp only [List.replicate_zero]
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
    wp_apply wp_slice_append_dfrac $$ [$Hsl $Hcap $Hl1]
      as %sl' ⟨Hsl, Hcap, -⟩
    · ipureintro; exact DFrac.valid_own_one
    (try wp_auto)
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists k, sl'
    simp only [named]
    have Htake : keys.take (p + 1).toNat = keys.take p.toNat ++ [k] := by
      rw [show (p + 1).toNat = p.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    rw [Htake]
    iframe
    ipureintro; omega
  · iintro HP Hm
    iNamed HP
    rw [← Hklen, Int.toNat_natCast, List.take_length]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    exact ⟨Hkset, Hknodup, rfl⟩

end proof

end sets
end EtcdGrove
end Perennial
