/-
Lean-first (no Rocq counterpart). Layer C's Probe (2026-11-08): the proof of `Server__copy`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Server__copy

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

theorem Server.copy.wp_proof : Server.copy.spec (GF := GF) (hG := hG) := by
  intro p v
  wp_start as #Hv
  iunfold serverRO at Hv
  icases Hv with ⟨%g, %mm, #Hp, %Hf, #Hl, #Hr, #Hg, #Hm, %Hmi, #Hc, #Hd⟩
  wp_auto
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  wp_auto
  wp_apply (wp_map_len (K := w64) (V := w64) g.MatchIndex' mm DFrac.discard) $$ [Hm] as -
  · iexact Hm
  wp_apply wp_map_make2 (K := w64) (V := w64) as %nm Hnm
  icases typedPointsto_not_null_dup _ _ _ $$ c with ⟨c, %Hcnn⟩
  icases typedPointsto_split _ _ _ $$ c with Hcf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcf
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (K := w64) (V := w64) (fun (keys : List w64) (i : Int) =>
      iprop(∃ (kv vv : w64) (mp : GMap w64 w64),
        "k" ∷ k_ptr ↦ kv ∗ "v" ∷ v_ptr ↦ vv ∗ "Hnm" ∷ nm ↦$ mp ∗
        "Hcm" ∷ c_ptr.[github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Server, go!"MatchIndex"] ↦ nm ∗
        "%Hmp" ∷ ⌜0 ≤ i ∧ ∀ x, mp !! x = if x ∈ keys.take i.toNat then mm !! x else none⌝))) $$ [Hm]
  · iexact Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknd⟩
  isplitl [k v Hnm MatchIndex]
  · iexists _, _, _
    iframe
    ipureintro
    refine ⟨Int.le_refl _, fun x => ?_⟩
    simp only [Int.toNat_zero, List.take_zero, List.not_mem_nil, if_false]
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
      rw [GMap.lookup_insert]; simp only [List.mem_append, List.mem_singleton, or_true, if_true, Hval]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hx), Hmp.2 x]
      simp only [List.mem_append, List.mem_singleton, hx, or_false]
  iintro HP Hm
  iNamed HP
  rw [show (GMap.size mm : Int).toNat = keys.length by omega, List.take_length] at Hmp
  have Hmpe : mp = mm := by
    apply GMap.map_eq; intro x
    rw [Hmp.2 x]
    split
    · rfl
    · rename_i hx
      cases h : mm !! x with
      | none => rfl
      | some y => exact absurd ((Hkset x).2 (by rw [h]; rfl)) hx
  subst Hmpe
  wp_auto
  ihave Hcp : c_ptr ↦ ({ g with MatchIndex' := nm } : G.Server) $$ [-HΦ Hnm]
  · iapply typedPointsto_combine _ _ _ Hcnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  iapply HΦ
  iunfold serverOwn
  iexists { g with MatchIndex' := nm }, mp
  iframe Hcp Hnm Hl Hr Hg Hc Hd
  ipureintro; exact ⟨Hf, Hmi⟩

end proof

end Etcdraft
end EtcdGrove
end Perennial
