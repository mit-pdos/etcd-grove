/-
Proof of `Spec/k8s_io/apimachinery/pkg/util/sets/KeySet.lean`. Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.sets.KeySet
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.sets

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]

theorem lookup_insertAll {K : Type} [DecidableEq K] (s : GMap K Elem) (ks : List K) (k : K) :
    insertAll s ks !! k = if k ∈ ks then some present else s !! k := by
  induction ks generalizing s with
  | nil => simp
  | cons a ks ih =>
    rw [insertAll_cons, ih]
    by_cases h : k ∈ ks
    · simp [h]
    · by_cases ha : a = k
      · subst ha; simp
      · simp [h, ha, Ne.symm ha]

theorem insertAll_keys {K V : Type} [DecidableEq K] (m : GMap K V) (keys : List K)
    (h : ∀ k, k ∈ keys ↔ (m !! k).isSome) : insertAll ∅ keys = keysOf m := by
  ext k
  rw [lookup_insertAll]
  unfold keysOf
  rw [GMap.lookup_fmap]
  by_cases hk : k ∈ keys
  · have := (h k).1 hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 this
    simp [hk, hv]
  · have : (m !! k) = none := by
      cases hm : m !! k with
      | none => rfl
      | some v => exact absurd ((h k).2 (by rw [hm]; rfl)) hk
    simp [hk, this]

theorem KeySet.wp_proof (wp_Insert : Set.Insert.spec (GF := GF) (hG := hG)) :
    KeySet.spec (GF := GF) (hG := hG) := by
  intro K V _ _ _ _ T _ _ _ _ Vt _ mref dq m
  wp_start as Hm
  wp_auto
  wp_apply wp_map_len $$ Hm as Hm
  rw [go.make2_underlying, (go.is_underlying : underlying (Set'.ty T) = _)]
  wp_apply (wp_map_make2 (K := K) (V := Elem) _ T Empty.ty) as %r Hr
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List K) (p : Int) => iprop(∃ (x : K),
      "%Hp" ∷ ⌜0 ≤ p⌝ ∗
      "keyValue" ∷ keyValue_ptr ↦ x ∗ "ret" ∷ ret_ptr ↦ r ∗
      "Hr" ∷ r ↦$ insertAll ∅ (keys.take p.toNat))) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [keyValue ret Hr]
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
    wp_apply (Set.wp_ptr_Insert_of wp_Insert) $$ [$ret $Hr $Hl1] as ⟨ret, Hr, -⟩
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
    rw [← Hklen, Int.toNat_natCast, List.take_length, insertAll_keys m keys Hkset]
    wp_auto
    iapply HΦ
    iframe

end proof

end sets
end EtcdGrove
end Perennial
