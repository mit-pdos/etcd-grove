module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__Clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__DeepCopyObject
public import Spec.maps.Clone
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ItemsRO

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Model.Clone.wp_proof
    (wp_DeepCopy : k8s_etcd3.Obj.DeepCopyObject.spec (GF := GF) (hG := hG))
    (wp_MapsClone : maps.Clone.spec_strBool (GF := GF) (hG := hG)) :
    Model.Clone.spec (GF := GF) (hG := hG) := by
  intro mp m
  wp_start as Hm
  unfold modelAt modelRep modelVal
  icases Hm with ⟨#Hinit, %il, %rl, %M, #Hp, #HI, #Hit, #HR⟩
  iStructNamed Hp
  wp_auto
  wp_apply (wp_map_len (t := go.GoType.MapType go.string k8s_io.apimachinery.pkg.runtime.Object.ty) il M DFrac.discard) $$ HI as -
  wp_apply (wp_map_make2 (K := GoString) (V := GoInterface) _ go.string
    k8s_io.apimachinery.pkg.runtime.Object.ty) as %il' Hil'
  wp_apply (wp_MapsClone rl m.rewrites DFrac.discard) $$ [HR] as %rl' ⟨-, Hrl'⟩
  · iexact HR
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (i : Int) => iprop(
      ∃ (Mc : GMap GoString GoInterface) (D : GMap GoString Obj) (xv : GoInterface) (xk : GoString),
      "%Hi" ∷ ⌜0 ≤ i ∧ ∀ k, D !! k = if k ∈ keys.take i.toNat then m.items !! k else none⌝ ∗
      "Hil'" ∷ il' ↦$ Mc ∗
      "#HD" ∷ itemsRO Mc D ∗
      "r0" ∷ «$r0_ptr» ↦ modelVal il' rl' m ∗
      "clone" ∷ clone_ptr ↦ «$r0_ptr» ∗
      "v" ∷ v_ptr ↦ xv ∗
      "k" ∷ k_ptr ↦ xk)) $$ HI
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hil' «$r0» clone v k]
  · iexists ∅, ∅, _, _
    simp only [named]
    ihave #HD := itemsRO_empty (GF := GF)
    unfold modelVal
    iframe
    isplitr
    · ipureintro; exact ⟨Int.le_refl _, fun k => by simp⟩
    · iexact HD
  isplitr
  · imodintro
    iintro %i %key %x ⟨%Hkey, %Hx⟩ HP
    iNamed HP
    icases itemsRO_lookup M m.items key x Hx $$ Hit with ⟨%p, %o, ⟨%ho, %hx⟩, #Hpo⟩
    subst hx
    wp_auto
    wp_apply (wp_DeepCopy p DFrac.discard o) $$ [Hpo] as %c ⟨-, Hc⟩
    · iexact Hpo
    ipersist Hc
    unfold modelVal
    wp_apply (wp_mapInsert go.string il' Mc key (objIface c)) $$ Hil' as Hil'
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    ihave %Hsz := itemsRO_size M m.items $$ Hit
    have hsub : (<[key := o]> D) ⊆ m.items := by
      intro k v hk
      show m.items !! k = some v
      by_cases hk' : key = k
      · subst hk'
        rw [show (<[key := o]> D).lookup key = (<[key := o]> D) !! key from rfl,
          GMap.lookup_insert] at hk
        rw [ho]; exact hk
      · rw [show (<[key := o]> D).lookup k = (<[key := o]> D) !! k from rfl,
          GMap.lookup_insert_ne _ _ hk', Hi.2 k] at hk
        split at hk
        · exact hk
        · cases hk
    ihave #HD' := itemsRO_insert Mc D key c o
      (Nat.le_trans (GMap.map_subseteq_size hsub) Hsz) $$ [HD Hc]
    · isplitl
      · iexact HD
      · iexact Hc
    iexists _, (<[key := o]> D), _, _
    simp only [named]
    iframe
    isplitr
    · ipureintro
      obtain ⟨Hi0, HiD⟩ := Hi
      refine ⟨by omega, fun k => ?_⟩
      have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
      rw [Htake]
      by_cases hk : key = k
      · subst hk
        rw [GMap.lookup_insert, if_pos (List.mem_append_right _ (List.mem_singleton_self _)), ho]
      · rw [GMap.lookup_insert_ne _ _ hk, HiD k]
        have : (k ∈ keys.take i.toNat ++ [key]) ↔ k ∈ keys.take i.toNat := by
          simp only [List.mem_append, List.mem_singleton]
          constructor
          · rintro (h | h)
            · exact h
            · exact absurd h.symm hk
          · exact Or.inl
        simp only [this]
    · iexact HD'
  iintro HP HI'
  iNamed HP
  ihave %hdom := itemsRO_dom_all M m.items $$ Hit
  have hD : D = m.items := by
    obtain ⟨-, HiD⟩ := Hi
    apply GMap.map_eq
    intro k
    rw [HiD k, Int.toNat_natCast, ← Hklen, List.take_length]
    by_cases hk : k ∈ keys
    · rw [if_pos hk]
    · rw [if_neg hk]
      have h1 : ¬ (M !! k).isSome := fun h => hk ((Hkset k).2 h)
      have h2 : ¬ (m.items !! k).isSome := fun h => h1 ((hdom k).2 h)
      cases h3 : m.items !! k
      · rfl
      · simp [h3] at h2
  rw [hD] at *
  wp_auto
  iapply HΦ
  unfold modelOwn modelRep
  iframe Hinit
  iexists il', rl', Mc
  iframe
  iexact HD

end proof

end k8s_correctness
end EtcdGrove
end Perennial
