/-
Lean-first (no Rocq counterpart).

The proof of `copyMap`: the loop's invariant is that the copy holds `m`'s entries at the keys
visited so far, and nothing else; at the end every key of `m` was visited.
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.copyMap

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

theorem copyMap.wp_proof : copyMap.spec (GF := GF) (hG := hG) := by
  intro l m dq
  wp_start as Hm
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoString)) as %c Hc
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (i : Int) => iprop(∃ (x y : GoString)
      (mv : GMap GoString GoString),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hmv" ∷ ⌜∀ k, mv !! k = if k ∈ keys.take i.toNat then m !! k else none⌝ ∗
      "k" ∷ k_ptr ↦ x ∗
      "v" ∷ v_ptr ↦ y ∗
      "c" ∷ c_ptr ↦ c ∗
      "Hc" ∷ c ↦$ mv)) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [k v c Hc]
  · iexists _, _, ∅
    simp only [named]
    iframe
    ipureintro
    refine ⟨Int.le_refl _, fun k => ?_⟩
    simp
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_mapInsert $$ Hc as Hc
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists key, vv, _
    simp only [named]
    iframe
    ipureintro
    refine ⟨by omega, fun k => ?_⟩
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    rw [Htake, GMap.lookup_insert_eq_iff]
    by_cases hk : key = k
    · subst hk; simp [Hvv]
    · simp only [hk, ↓reduceIte]; rw [Hmv]
      simp [List.mem_append, Ne.symm hk]
  iintro HP Hm
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hmv
  have Hmv' : mv = m := by
    apply GMap.map_eq; intro k
    rw [Hmv k]
    by_cases hk : k ∈ keys
    · simp only [hk, ↓reduceIte]
    · simp only [hk, ↓reduceIte]
      have := mt (Hkset k).mpr hk
      cases h : m !! k <;> simp_all
  subst Hmv'
  wp_auto
  iapply HΦ
  iframe

end proof

end kvwitness
end EtcdGrove
end Perennial
