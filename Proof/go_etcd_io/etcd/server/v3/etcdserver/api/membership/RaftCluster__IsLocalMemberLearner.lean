/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__IsLocalMemberLearner.lean`.
Lean-first (no Rocq counterpart); D43 M4 (2026-10-26): under the cluster's mutex, a lookup of the
local id in the members map, the member's `IsLearner` read if found (its record owned in the
map, `rcLockInv`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__IsLocalMemberLearner

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A member's `IsLearner` field, borrowed. -/
theorem membership.ownMember_isLearner_acc (m : Loc) :
    membership.ownMember (GF := GF) m ⊢ ∃ il : Bool,
      membership.mIsLearnerAddr m ↦ il ∗ (membership.mIsLearnerAddr m ↦ il -∗ membership.ownMember m) := by
  unfold membership.ownMember membership.memberIs
  iintro ⟨%id, %Hnn, %pu, %cu, %il, %nm, %pus, %cus, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus, %Hpok⟩
  iexists il
  iframe Hil
  iintro Hil
  iexists id
  isplitr
  · ipureintro; exact Hnn
  iexists pu, cu, il, nm, pus, cus
  iframe
  ipureintro; exact Hpok

theorem membership.RaftCluster.IsLocalMemberLearner.wp_proof :
    membership.RaftCluster.IsLocalMemberLearner.spec (GF := GF) (hG := hG) := by
  intro c RM
  wp_start as #Hrc
  iunfold membership.isRaftClusterG at Hrc
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hrc] as ⟨Hlocked, Hinv⟩
  iunfold membership.rcLockInvG at Hinv
  icases Hinv with ⟨%mp, %mm, Hmf, Hmap, %Hsz, Hmems, %lid, %rp, %rm, #Hlid, Hrf, Hrm, HRM⟩
  (try wp_auto)
  wp_apply wp_map_lookup2 _ _ mp mm lid (DFrac.own 1) $$ [$Hmap] as Hmap
  (try wp_auto)
  -- the lock invariant, as it was
  ihave Hclose : iprop(membership.rcMembersAddr c ↦ mp -∗ mp ↦$ mm -∗
      ([∗map] _k ↦ m ∈ mm, membership.ownMember m) -∗ membership.rcLockInvG c RM)
    $$ [Hrf Hrm HRM]
  · iintro Hmf Hmap Hmems
    iunfold membership.rcLockInvG
    iexists mp, mm
    iframe Hmf Hmap Hmems
    isplitr
    · ipureintro; exact Hsz
    iexists lid, rp, rm
    iframe
    iexact Hlid
  cases Hm : mm !! lid with
  | none =>
    -- (the fork's fix) the local member removed: no learner
    simp only [Option.getD_none, Option.isSome_none]
    (try wp_auto)
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmf Hmap Hmems Hclose]
    · inext
      iapply Hclose $$ Hmf Hmap Hmems
    (try wp_auto)
    iapply HΦ
    itrivial
  | some m =>
    simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
    (try wp_auto)
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun _ m => membership.ownMember (GF := GF) m) Hm).1
      $$ Hmems with ⟨Hmem, Hmems⟩
    icases membership.ownMember_isLearner_acc m $$ Hmem with ⟨%il, Hil, Hmem⟩
    wp_auto
    ihave Hmem := Hmem $$ Hil
    ihave Hmems := Hmems $$ Hmem
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmf Hmap Hmems Hclose]
    · inext
      iapply Hclose $$ Hmf Hmap Hmems
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
