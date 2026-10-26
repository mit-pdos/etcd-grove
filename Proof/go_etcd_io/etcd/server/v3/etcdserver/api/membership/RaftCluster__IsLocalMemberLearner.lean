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
  icases Hinv with ⟨%mm, %mem, Hmem, %Hsz, %lid, %rp, %rm, #Hlid, Hrf, Hrm, HRM⟩
  icases membership.memAt_open c _ mm mem $$ Hmem with ⟨%mp, Hfl, Hmap, Hmems, Hmf⟩
  (try wp_auto)
  wp_apply wp_map_lookup2 _ _ mp mm lid (DFrac.own (1 : Qp).half) $$ [$Hmap] as Hmap
  (try wp_auto)
  -- the lock invariant, as it was
  ihave Hclose : iprop(membership.rcMembersAddr c ↦{DFrac.own (1 : Qp).half} mp -∗
      mp ↦${DFrac.own (1 : Qp).half} mm -∗
      ([∗map] k ↦ m ∈ mm, membership.memberAt m (1 : Qp).half ((mem !! k).getD default)) -∗
      membership.rcLockInvG c RM)
    $$ [Hmf Hrf Hrm HRM]
  · iintro Hfl Hmap Hmems
    iunfold membership.rcLockInvG
    iexists mm, mem
    isplitl [Hmf Hfl Hmap Hmems]
    · iapply Hmf $$ Hfl Hmap Hmems
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
    wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hfl Hmap Hmems Hclose]
    · inext
      iapply Hclose $$ Hfl Hmap Hmems
    (try wp_auto)
    iapply HΦ
    itrivial
  | some m =>
    simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
    (try wp_auto)
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun k m => membership.memberAt (GF := GF) m
      (1 : Qp).half ((mem !! k).getD default)) Hm).1 $$ Hmems with ⟨Hmem, Hmems⟩
    icases membership.memberAt_isLearner_acc m _ _ $$ Hmem with ⟨Hil, Hmem⟩
    wp_auto
    ihave Hmem := Hmem $$ Hil
    ihave Hmems := Hmems $$ Hmem
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hfl Hmap Hmems Hclose]
    · inext
      iapply Hclose $$ Hfl Hmap Hmems
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
