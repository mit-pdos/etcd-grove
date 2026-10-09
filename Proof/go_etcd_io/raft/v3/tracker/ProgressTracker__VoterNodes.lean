/-
Port of `election_proof/proof_ProgressTracker__VoterNodes.v`.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__VoterNodes
public import Spec.go_etcd_io.raft.v3.quorum.JointConfig__IDs
public import Spec.slices.Sort

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `IDs()`, then `make([]uint64, 0, len(m))`, a `for range` appending each key, and
`slices.Sort`. The tracker is opened only for `Hcfg_size` (the `make3` and `Sort` bounds) and
re-sealed at once. The loop invariant is that `nodes` holds the first `i` keys of the
enumeration `wp_map_for_range` picks. -/
theorem tracker.ProgressTracker.VoterNodes.wp_proof
    (wp_JointConfig_IDs : quorum.JointConfig.IDs.spec (GF := GF) (hG := hG))
    (wp_slices_Sort : slices.«Sort».spec (GF := GF) (hG := hG)) :
    tracker.ProgressTracker.VoterNodes.spec (GF := GF) (hG := hG) := by
  intro cfg trk tv t
  wp_start as ⟨Htrk, Hown⟩
  wp_auto
  wp_apply (quorum.JointConfig.IDs.spec_tracker wp_JointConfig_IDs) $$ [$Htrk $Hown] as %mref %idm ⟨Htrk, Hown, Hidm, %Hdomidm⟩
  iNamed Hown
  ihave Hown := ownTracker_intro cfg tv t.votes t.prs t.peers voters_ref voters
    learners learnersNext Hprs_dom Hvoters_arr Hautoleave Hvoters_dom Hno_learners Hcfg_size
    HmaxInfl $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext
  wp_apply wp_map_len $$ Hidm as Hidm
  have Hszidm : GMap.size idm = GMap.size cfg := by
    rw [← Hdomidm, GMap.size_dom]
  rw [Hszidm]
  wp_apply wp_slice_make3 (V := w64) (t := go.uint64) (W64 0) (W64 (GMap.size cfg))
    (by word) as %sl ⟨Hsl, Hsl_cap, %Hslcap⟩
  simp only [List.replicate_zero]
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (sl' : GoSlice) (x : w64),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "nodes" ∷ nodes_ptr ↦ sl' ∗
      "Hsl" ∷ sl' ↦* keys.take i.toNat ∗
      "Hsl_cap" ∷ ownSliceCap w64 sl' (DFrac.own 1) ∗
      "id" ∷ id_ptr ↦ x)) $$ Hidm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [nodes Hsl Hsl_cap id]
  · iexists sl, zero_val w64
    simp only [Int.toNat_zero, List.take_zero]
    iframe
    ipureintro
    omega
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_slice_literal (V := w64) [key]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hsl $Hsl_cap $Hsl2] as %sl3 ⟨Hsl, Hsl_cap, -⟩
    unfold forMapPostcondition
    iright
    ileft
    isplitr
    · ipureintro; rfl
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    iexists sl3, key
    rw [Htake]
    iframe
    ipureintro
    omega
  iintro HP -
  iNamed HP
  rw [← Hklen, Int.toNat_natCast, List.take_length]
  wp_auto
  wp_apply wp_slices_Sort $$ [$Hsl] as %xs ⟨Hsl, %Hxs, -⟩
  · ipureintro; omega
  iapply HΦ
  iframe
  ipureintro
  refine Hxs.symm.trans ((List.perm_ext_iff_of_nodup Hknodup (GMap.NoDup_elements cfg)).2 ?_)
  intro k
  rw [Hkset, GMap.elem_of_elements, ← Hdomidm, GMap.elem_of_dom]
  cases idm !! k <;> simp

end proof

end EtcdGrove
end Perennial
