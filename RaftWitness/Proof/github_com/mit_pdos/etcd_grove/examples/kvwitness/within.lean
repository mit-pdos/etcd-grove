/-
Lean-first (no Rocq counterpart).

The proof of `within`: the loop's invariant is that `ok` says whether the keys of `a` visited
so far have their value in `b`.
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.within

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

theorem within.wp_proof : within.spec (GF := GF) (hG := hG) := by
  intro la lb ma mb dqa dqb
  wp_start as ⟨Ha, Hb⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (i : Int) => iprop(∃ (x y : GoString)
      (b : Bool),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hb" ∷ ⌜b = true ↔ ∀ k v, k ∈ keys.take i.toNat → ma !! k = some v →
        (mb !! k).getD [] = v⌝ ∗
      "k" ∷ k_ptr ↦ x ∗
      "v" ∷ v_ptr ↦ y ∗
      "ok" ∷ ok_ptr ↦ b ∗
      "bp" ∷ b_ptr ↦ lb ∗
      "Hmb" ∷ lb ↦${dqb} mb)) $$ Ha
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [k v ok b Hb]
  · iexists _, _, true
    simp only [named]
    iframe
    ipureintro
    refine ⟨Int.le_refl _, ?_⟩
    simp
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_map_lookup1 $$ Hmb as Hmb
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    wp_if_destruct
    · unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists key, _, b
      simp only [named]
      iframe
      ipureintro
      refine ⟨by omega, ?_⟩
      rw [Htake, Hb]
      constructor
      · intro H k v hk hv
        rcases List.mem_append.mp hk with hk | hk
        · exact H k v hk hv
        · rw [List.mem_singleton] at hk
          subst hk
          rw [Hvv] at hv
          cases hv
          rfl
      · intro H k v hk hv
        exact H k v (List.mem_append_left _ hk) hv
    · unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists key, vv, false
      simp only [named]
      iframe
      ipureintro
      refine ⟨by omega, ?_⟩
      rw [Htake]
      simp only [Bool.false_eq_true, false_iff]
      intro H
      exact Hif (H key vv (List.mem_append_right _ (List.mem_singleton_self _)) Hvv)
  iintro HP Ha
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hb
  wp_auto
  iapply HΦ
  iframe
  ipureintro
  rw [Hb]
  constructor
  · intro H k v hv
    exact H k v ((Hkset k).mpr (by simp [hv])) hv
  · intro H k v _ hv
    exact H k v hv

end proof

end kvwitness
end EtcdGrove
end Perennial
