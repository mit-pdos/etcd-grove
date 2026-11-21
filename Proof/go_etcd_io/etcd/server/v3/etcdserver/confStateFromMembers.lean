/- Reconstruction of a pre-3.5 backend's ConfState from its saved members. -/
module
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
open go_etcd_io.raft.v3

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- Both output slices follow the same Go map enumeration, partitioned by the stored
learner bit. The IDs are read from the members themselves. -/
theorem wp_confStateFromMembers (mp : Loc) (ptrs : GMap w64 Loc) (dq : DFrac)
    (memberID : w64 → w64) (learner : w64 → Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ mp ↦${dq} ptrs ∗
      □ (∀ (key : w64) (p : Loc), ⌜ptrs !! key = some p⌝ -∗
        membership.mIDAddr p ↦□ memberID key ∗ membership.mIsLearnerAddr p ↦□ learner key) }}
      (App (Val (@! confStateFromMembers)) (Val #mp))
    {{ (cs : raftpb.ConfState), RET #cs; mp ↦${dq} ptrs ∗ ∃ keys : List w64,
      ⌜(∀ k, k ∈ keys ↔ (ptrs !! k).isSome) ∧ keys.Nodup ∧
        cs = { (zero_val raftpb.ConfState) with Voters' := cs.Voters', Learners' := cs.Learners' }⌝ ∗
      cs.Voters' ↦* ((keys.filter (fun k => !(learner k))).map memberID) ∗
      cs.Learners' ↦* ((keys.filter learner).map memberID) }} := by
  wp_start as ⟨Hmap, #Hmembers⟩
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := Loc) (fun (keys : List w64) (i : Int) => iprop(
    ∃ (v l : GoSlice) (p : Loc), "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "voters" ∷ voters_ptr ↦ v ∗ "learners" ∷ learners_ptr ↦ l ∗ "m" ∷ m_ptr ↦ p ∗
      "Hv" ∷ v ↦* (((keys.take i.toNat).filter (fun k => !(learner k))).map memberID) ∗
      "Hl" ∷ l ↦* (((keys.take i.toNat).filter learner).map memberID) ∗
      "Hvc" ∷ ownSliceCap w64 v (DFrac.own 1) ∗ "Hlc" ∷ ownSliceCap w64 l (DFrac.own 1))) $$ Hmap
  iintro %keys ⟨%hkeys, %hlen, %hnodup⟩
  isplitl [voters learners m]
  · iexists slice.nil, slice.nil, zero_val Loc
    simp only [named, Int.toNat_zero, List.take_zero, List.filter_nil, List.map_nil]
    iframe voters learners m
    isplitr; · ipureintro; decide
    isplitr; · iapply ownSlice_nil
    isplitr; · iapply ownSlice_nil
    isplitr <;> iapply ownSliceCap_nil
  isplitr
  · imodintro
    iintro %i %key %memPtr ⟨%hk, %hp⟩ HP
    iNamed HP
    ihave ⟨#Hid, #Hlearner⟩ := Hmembers $$ %key %memPtr %hp
    have htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, hk]; rfl
    (try wp_auto)
    cases h : learner key <;> (try wp_auto)
    all_goals
      wp_apply wp_slice_literal (V := w64) [memberID key]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hs, -⟩
      (try wp_auto)
    · wp_apply wp_slice_append $$ [$Hv $Hvc $Hs] as %v' ⟨Hv, Hvc, -⟩
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft; isplitr; · ipureintro; rfl
      iexists v', l, memPtr
      simp [named, htake, h]
      iframe
      ipureintro; omega
    · wp_apply wp_slice_append $$ [$Hl $Hlc $Hs] as %l' ⟨Hl, Hlc, -⟩
      (try wp_auto)
      unfold forMapPostcondition
      iright; ileft; isplitr; · ipureintro; rfl
      iexists v, l', memPtr
      simp [named, htake, h]
      iframe
      ipureintro; omega
  iintro HP Hmap
  iNamed HP
  rw [← hlen, Int.toNat_natCast, List.take_length]
  (try wp_auto)
  iapply HΦ
  iframe Hmap
  iexists keys
  iframe Hv Hl
  ipureintro; exact ⟨hkeys, hnodup, rfl⟩

end EtcdGrove
end Perennial
