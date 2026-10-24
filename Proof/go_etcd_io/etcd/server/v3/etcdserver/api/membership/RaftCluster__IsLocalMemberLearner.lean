/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__IsLocalMemberLearner.lean`.
Lean-first (no Rocq counterpart); PR #22188 verification.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__IsLocalMemberLearner
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Debug

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

theorem membership.RaftCluster.IsLocalMemberLearner.wp_proof
    (wp_IDString : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (wp_ZapString : zap.String.spec (GF := GF) (hG := hG))
    (wp_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG)) :
    membership.RaftCluster.IsLocalMemberLearner.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as #Hrc
  iunfold membership.isRaftCluster at Hrc
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Htypes : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hrc] as ⟨Hlocked, Hinv⟩
  iunfold membership.rcLockInv at Hinv
  icases Hinv with ⟨%mp, %mm, Hmf, Hmap, %Hsz, Hmems, #Hloc, %rp, Hrf, Hrm⟩
  iunfold membership.rcLocalIn at Hloc
  icases Hloc with ⟨%lid, %cid, %lg, #Hlid, #Hcid, #Hlg, %Hlgnn⟩
  (try wp_auto)
  wp_apply wp_map_lookup2 _ _ mp mm lid (DFrac.own 1) $$ [$Hmap] as Hmap
  cases hlookup : mm !! lid with
  | none =>
    simp only [Option.getD_none, Option.isSome_none]
    (try wp_auto)
    wp_apply wp_IDString (membership.rcCidAddr c) DFrac.discard cid $$ [$Hcid] as %s0 ⟨_, %_⟩
    (try wp_auto)
    wp_apply wp_ZapString as %f0 -
    (try wp_auto)
    wp_apply wp_IDString (membership.rcLocalIDAddr c) DFrac.discard lid $$ [$Hlid] as %s1 ⟨_, %_⟩
    (try wp_auto)
    wp_apply wp_ZapString as %f1 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f0, f1]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply wp_Debug lg
    · iframe #; ipureintro; exact Hlgnn
    (try wp_auto)
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmf Hmap Hmems Hrf Hrm]
    · inext
      iunfold membership.rcLockInv
      iexists mp, mm
      iframe Hmf Hmap Hmems
      isplitr
      · ipureintro; exact Hsz
      isplitr
      · iunfold membership.rcLocalIn
        iexists lid, cid, lg
        iframe #
        ipureintro; exact Hlgnn
      iexists rp
      iframe
    (try wp_auto)
    iapply HΦ
    itrivial
  | some m =>
    simp only [Option.getD_some, Option.isSome_some]
    ihave ⟨Hm, Hback⟩ :=
      (BigSepM.bigSepM_lookup_acc (Φ := fun (_ : w64) (x : Loc) =>
        membership.ownMember (GF := GF) x) hlookup).1 $$ Hmems
    ihave ⟨%Hmnn, %il, Hil, Hback_m⟩ := membership.ownMember_isLearner_acc m $$ Hm
    (try wp_auto)
    ihave Hm := Hback_m $$ Hil
    ihave Hmems := Hback $$ Hm
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmf Hmap Hmems Hrf Hrm]
    · inext
      iunfold membership.rcLockInv
      iexists mp, mm
      iframe Hmf Hmap Hmems
      isplitr
      · ipureintro; exact Hsz
      isplitr
      · iunfold membership.rcLocalIn
        iexists lid, cid, lg
        iframe #
        ipureintro; exact Hlgnn
      iexists rp
      iframe
    (try wp_auto)
    iapply HΦ
    itrivial

theorem membership.RaftCluster.IsLocalMemberLearner_absent.wp_proof
    (wp_IDString : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (wp_ZapString : zap.String.spec (GF := GF) (hG := hG))
    (wp_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG)) :
    membership.RaftCluster.IsLocalMemberLearner_absent.spec (GF := GF) (hG := hG) := by
  intro c lid
  wp_start as #Hmu
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Htypes : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  icases Hinv with ⟨%mp, %lg, %ms, %cid, Hmf, Hmap, #Hlid, #Hcid, #Hlg, %Hlgnn, %Hnone⟩
  (try wp_auto)
  wp_apply wp_map_lookup2 _ _ mp ms lid (DFrac.own 1) $$ [$Hmap] as Hmap
  rw [Hnone]
  simp only [Option.getD_none, Option.isSome_none]
  (try wp_auto)
  wp_apply wp_IDString (membership.rcCidAddr c) DFrac.discard cid $$ [$Hcid] as %s0 ⟨_, %_⟩
  (try wp_auto)
  wp_apply wp_ZapString as %f0 -
  (try wp_auto)
  wp_apply wp_IDString (membership.rcLocalIDAddr c) DFrac.discard lid $$ [$Hlid] as %s1 ⟨_, %_⟩
  (try wp_auto)
  wp_apply wp_ZapString as %f1 -
  (try wp_auto)
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f0, f1]
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  wp_apply wp_Debug lg
  · iframe #; ipureintro; exact Hlgnn
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hmf Hmap]
  · inext
    iexists mp, lg, ms, cid
    iframe Hmf Hmap
    iframe #
    ipureintro; exact ⟨Hlgnn, Hnone⟩
  (try wp_auto)
  iapply HΦ
  itrivial

theorem membership.RaftCluster.IsLocalMemberLearner_present.wp_proof :
    membership.RaftCluster.IsLocalMemberLearner_present.spec (GF := GF) (hG := hG) := by
  intro c lid il
  wp_start as #Hmu
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  icases Hinv with ⟨%mp, %m, %ms, Hmf, Hmap, #Hlid, Hil, %Hmnn, %Hsome⟩
  (try wp_auto)
  wp_apply wp_map_lookup2 _ _ mp ms lid (DFrac.own 1) $$ [$Hmap] as Hmap
  rw [Hsome]
  simp only [Option.getD_some, Option.isSome_some]
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hmf Hmap Hil]
  · inext
    iexists mp, m, ms
    iframe Hmf Hmap Hil
    iframe #
    ipureintro; exact ⟨Hmnn, Hsome⟩
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
