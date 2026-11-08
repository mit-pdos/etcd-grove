/-
Lean-first (no Rocq counterpart). Layer C's Probe (2026-11-08): the proof of `State__clone`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem State.clone.wp_proof : State.clone.spec (GF := GF) (hG := hG) := by
  intro p st
  wp_start as #Hst
  iunfold stateRO at Hst
  icases Hst with ⟨%g, %sm, #Hp, #Hsrv, #Hm, %Hkeys, #Hsrvs, #Hb1, #Hb2, %Hrc⟩
  wp_auto
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  wp_auto
  wp_apply (wp_map_len (K := w64) (V := Loc) g.S' sm DFrac.discard) $$ [Hm] as -
  · iexact Hm
  wp_apply wp_map_make2 (K := w64) (V := Loc) as %nm Hnm
  icases typedPointsto_not_null_dup _ _ _ $$ c with ⟨c, %Hcnn⟩
  icases typedPointsto_split _ _ _ $$ c with Hcf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcf
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (K := w64) (V := Loc) (fun (keys : List w64) (i : Int) =>
      iprop(∃ (kv : w64) (vv : Loc) (mp : GMap w64 Loc),
        "k" ∷ k_ptr ↦ kv ∗ "v" ∷ v_ptr ↦ vv ∗ "Hnm" ∷ nm ↦$ mp ∗
        "Hcm" ∷ c_ptr.[github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State, go!"S"] ↦ nm ∗
        "%Hmp" ∷ ⌜0 ≤ i ∧ ∀ x, mp !! x = if x ∈ keys.take i.toNat then sm !! x else none⌝))) $$ [Hm]
  · iexact Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknd⟩
  isplitl [k v Hnm S]
  · iexists _, _, _
    iframe
    ipureintro
    refine ⟨Int.le_refl _, fun x => ?_⟩
    simp only [Int.toNat_zero, List.take_zero, List.not_mem_nil, ite_false]
    rfl
  isplitr
  · imodintro
    iintro %i %key %val ⟨%Hkey, %Hval⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_mapInsert $$ [Hnm] as Hnm
    · iexact Hnm
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists key, val, _
    iframe
    ipureintro
    refine ⟨by omega, fun x => ?_⟩
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    rw [Htake]
    by_cases hx : x = key
    · subst hx
      rw [GMap.lookup_insert]; simp only [List.mem_append, List.mem_singleton, or_true, ite_true, Hval]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hx), Hmp.2 x]
      simp only [List.mem_append, List.mem_singleton, hx, or_false]
  iintro HP Hm
  iNamed HP
  rw [show (GMap.size sm : Int).toNat = keys.length by omega, List.take_length] at Hmp
  have Hmpe : mp = sm := by
    apply GMap.map_eq; intro x
    rw [Hmp.2 x]
    split
    · rfl
    · rename_i hx
      cases h : sm !! x with
      | none => rfl
      | some y => exact absurd ((Hkset x).2 (by rw [h]; rfl)) hx
  subst Hmpe
  wp_auto
  ihave Hcp : c_ptr ↦ ({ g with S' := nm } : G.State) $$ [-HΦ Hnm]
  · iapply typedPointsto_combine _ _ _ Hcnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply HΦ
  iunfold stateOwn
  iexists { g with S' := nm }, mp
  iframe Hcp Hnm Hsrv Hb1 Hb2
  isplitr
  · ipureintro; exact Hkeys
  isplitl
  · simp only [List.not_mem_nil, ite_false]
    iexact Hsrvs
  ipureintro; exact Hrc

end proof

end Etcdraft
end EtcdGrove
end Perennial
