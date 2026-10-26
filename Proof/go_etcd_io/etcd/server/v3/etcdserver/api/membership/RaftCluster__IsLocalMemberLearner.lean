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
  intro c
  wp_start as #Hrc
  iunfold membership.isRaftCluster at Hrc
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hrc] as ⟨Hlocked, Hinv⟩
  iunfold membership.rcLockInv at Hinv
  icases Hinv with ⟨%mp, %mm, Hmf, Hmap, %Hsz, Hmems, #Hloc, %rp, Hrf, Hrm⟩
  ihave #Hloc' := Hloc
  iunfold membership.rcLocalIn at Hloc'
  icases Hloc' with ⟨%lid, #Hlid, %Hin⟩
  (try wp_auto)
  wp_apply wp_map_lookup2 _ _ mp mm lid (DFrac.own 1) $$ [$Hmap] as Hmap
  (try wp_auto)
  obtain ⟨m, Hm⟩ := Option.ne_none_iff_exists'.1 Hin
  rw [Hm]
  simp only [Option.getD_some, Option.isSome_some, decide_true]
  (try wp_auto)
  icases (BigSepM.bigSepM_lookup_acc (Φ := fun _ m => membership.ownMember (GF := GF) m) Hm).1
    $$ Hmems with ⟨Hmem, Hmems⟩
  icases membership.ownMember_isLearner_acc m $$ Hmem with ⟨%il, Hil, Hmem⟩
  wp_auto
  ihave Hmem := Hmem $$ Hil
  ihave Hmems := Hmems $$ Hmem
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmf Hmap Hmems Hrf Hrm]
  · inext
    iunfold membership.rcLockInv
    iexists mp, mm
    iframe Hmf Hmap Hmems Hloc
    isplitr
    · ipureintro; exact Hsz
    iexists rp
    iframe
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
