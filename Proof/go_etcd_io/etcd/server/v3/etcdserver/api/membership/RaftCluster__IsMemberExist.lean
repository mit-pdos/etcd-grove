/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__IsMemberExist.lean`.
Lean-first (no Rocq counterpart); PR #22188 verification.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__IsMemberExist

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

theorem membership.RaftCluster.IsMemberExist.wp_proof :
    membership.RaftCluster.IsMemberExist.spec (GF := GF) (hG := hG) := by
  intro c id
  wp_start as #Hrc
  iunfold membership.isRaftCluster at Hrc
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hrc] as ⟨Hlocked, Hinv⟩
  iunfold membership.rcLockInv at Hinv
  icases Hinv with ⟨%mp, %mm, Hmf, Hmap, %Hsz, Hmems, #Hloc, %rp, Hrf, Hrm⟩
  (try wp_auto)
  wp_apply wp_map_lookup2 _ _ mp mm id (DFrac.own 1) $$ [$Hmap] as Hmap
  (try wp_auto)
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

theorem membership.RaftCluster.IsMemberExist_exact.wp_proof :
    membership.RaftCluster.IsMemberExist_exact.spec (GF := GF) (hG := hG) := by
  intro c id b
  wp_start as #Hmu
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  icases Hinv with ⟨%mp, %ms, Hmf, Hmap, %Hb⟩
  (try wp_auto)
  wp_apply wp_map_lookup2 _ _ mp ms id (DFrac.own 1) $$ [$Hmap] as Hmap
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hmf Hmap]
  · inext
    iexists mp, ms
    iframe Hmf Hmap
    ipureintro; exact Hb
  (try wp_auto)
  have hEq : decide ((ms !! id).isSome = true) = b := by
    rw [Hb]; cases b <;> rfl
  rw [hEq]
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
