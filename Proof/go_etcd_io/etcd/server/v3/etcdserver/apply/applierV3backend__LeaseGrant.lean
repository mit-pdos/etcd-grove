/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__LeaseGrant
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__newHeader
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.KVLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.applierV3backend.LeaseGrant.wp_proof
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.LeaseGrant.spec (GF := GF) (hG := hG) := by
  intro E p r rq g log T rs U Pre Q Post info
  -- `lean`'s proof (the lease-grant stage's triple) with the backend's tokens (`mPreW_split`,
  -- `mPostW_backend`, `threadTok`, `newHeader`'s `E.Nx`)
  wp_start as ⟨#Hb, Htt, Hgp⟩
  iunfold apply.grantPre at Hgp
  icases Hgp with ⟨%Hrq, #Hr, #Hgr, HltT, HRO, Hpre, -, HU, HUf⟩
  obtain ⟨Hlg, Hg, Hk⟩ := Hrq
  icases apply.mPreW_split $$ Hpre with ⟨%cr, %B, Hsw, Hcs, Hwt, Hrt, Htie, Hres, Hkv⟩
  iunfold apply.kvRest at Hkv
  icases Hkv with ⟨Hbk, Hhk, Hlive, Hard⟩
  iunfold apply.leasesLive at Hlive
  icases Hlive with ⟨%L, #Hknown, Hu, HltL⟩
  ihave %HLT := apply.ltHalf_agree E L T Hlg $$ [HltL HltT]
  · iframe HltL HltT
  subst HLT
  iunfold EtcdGrove.lease.lessorUser at Hu
  icases Hu with ⟨Hown, Hrdo, Hrvk⟩
  ihave #Hb' := Hb
  iunfold apply.backendIs at Hb'
  icases Hb' with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨%Hlgn, -, -, -, #Hle, -⟩
  iunfold apply.isApplyLessor at Hle
  icases Hle with ⟨-, %li, %Hli, #HGrant, -⟩
  ihave #Hr' := Hr
  iunfold apply.leaseGrantIs at Hr'
  icases Hr' with ⟨%Hrn, #Hid, #Httl⟩
  iStructNamed Hopts
  wp_auto
  rw [Hli]
  wp_auto
  wp_apply HGrant $$ [$Hcs $HRO $Hown $Hrvk $Hwt $Hrt $Htie $Hgr $HU $HUf] as %l %err
    ⟨Hrt, Htie, #HeI, Hres'⟩
  icases Hres' with (⟨%Hne, #HlE, HPre, Hown, Hrvk, HRO, HU⟩ |
    ⟨%Hok, HPost, Hown, Hrvk, #Hlease, #Hlf, HU, #Hreq, ⟨%t, #Hlt, %Htge, HRO⟩⟩)
  · ihave HPP : iprop(Post ∨ Pre) $$ [HPre]
    · iright; iexact HPre
    ihave Hlive : apply.leasesLive E (mvcc.stateAfter log) $$ [Hown Hrdo Hrvk HltL]
    · iunfold apply.leasesLive
      iexists L
      isplitl []
      · iexact Hknown
      iunfold EtcdGrove.lease.lessorUser
      iframe Hown Hrdo Hrvk HltL
    cases err with
    | nil => exact absurd rfl Hne.1
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe Htt
      iexists (Outcome.rejected .backend)
      iunfold apply.grantPost
      isplitl [Hsw Htie Hbk Hhk Hlive Hard HPP Hrt]
      · iapply (apply.mPostW_backend _ _ _ _ _ B cr)
        iframe Hsw Htie HPP Hrt
        iunfold apply.kvRest
        iframe
      iframe HeI
      isplitr
      · iintro %_; iexact HlE
      isplitr
      · ipureintro
        refine ⟨?_, ?_, ?_⟩
        · simp [apply.chainStep, apply.backendStep, Hk]
        · constructor
          · rintro ⟨_, _, h⟩; cases h
          · intro h; cases h
        · constructor
          · intro h; cases h
          · rintro ⟨-, h⟩; exact absurd h Hne.2
      rw [apply.grantIds_rejected, apply.grantIds_rejected]
      iframe HltT HU
      isplitl [HRO]
      · iexists g.ttl
        isplitr
        · ipureintro; exact apply.grantTTLOk_of rq g _ Hg (Int.le_refl _)
        rw [apply.grantRest_rejected]; iexact HRO
      iunfold apply.grantAnswer
      rw [Hg]
      iexists _
      isplitr
      · ipureintro; rfl
      iright; ipureintro; exact Hne.1
  · obtain ⟨He, Hgi⟩ := Hok
    subst He
    ihave HPP : iprop(Post ∨ Pre) $$ [HPost]
    · ileft; iexact HPost
    imod apply.ltHalf_update E L L (L ++ [g.id]) $$ HltL HltT with ⟨HltL, HltT⟩
    ihave Hlive : apply.leasesLive E (mvcc.stateAfter log) $$ [Hown Hrdo Hrvk HltL]
    · iunfold apply.leasesLive
      iexists (L ++ [g.id])
      isplitl []
      · iapply EtcdGrove.apply.leasesKnown_mono L (L ++ [g.id]) _
          (fun x hx => List.mem_append_left _ hx) $$ Hknown
      iunfold EtcdGrove.lease.lessorUser
      iframe Hown Hrdo Hrvk HltL
    iunfold apply.leaseTTLIs at Hlease
    icases Hlease with ⟨%Hln, #HlID, #HTTL⟩
    icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨Hr0, %Hnn⟩
    iStructNamed Hr0
    wp_auto
    wp_apply HTTL as %tt -
    iapply wp_fupd
    wp_apply (hHdr E p log cr) $$ [$Hpkg $Hb $Htt $Hsw] as %h ⟨Htt, Hsw, %Hh, Hhf, Hrev, Hnx, %Hlen⟩
    ipersist ID
    ipersist TTL
    ipersist Error
    ipersist Header
    ipersist Hrev
    iapply HΦ
    iframe Htt
    iexists (Outcome.applied log false)
    iunfold apply.grantPost
    isplitl [Hsw Htie Hbk Hhk Hlive Hard HPP Hrt]
    · iapply (apply.mPostW_backend _ _ _ _ _ B cr)
      iframe Hsw Htie HPP Hrt
      iunfold apply.kvRest
      iframe
    isplitr
    · iapply applyErrIs_nil
    isplitr
    · iintro %h; cases h
    isplitr
    · ipureintro
      refine ⟨?_, ?_, ?_⟩
      · simp [apply.chainStep, apply.backendStep, Hk]
      · exact ⟨fun _ => rfl, fun _ => ⟨log, false, rfl⟩⟩
      · exact ⟨fun _ => ⟨rfl, Hgi⟩, fun _ => rfl⟩
    rw [apply.grantIds_applied rq g log false L Hk Hg, apply.grantIds_applied rq g log false U Hk Hg]
    iframe HltT HU
    isplitl [HRO]
    · iexists t
      isplitr
      · ipureintro; exact apply.grantTTLOk_of rq g t Hg Htge
      rw [apply.grantRest_applied t rq g log false rs Hk Hg]; iexact HRO
    iunfold apply.grantAnswer
    rw [Hg]
    iexists _
    isplitr
    · ipureintro; rfl
    ileft
    isplitr
    · ipureintro; rfl
    isplitl [Hhf Hnx]
    · iunfold apply.grantRespIs
      isplitr
      · ipureintro; exact Hnn
      iframe ID
      isplitr
      · iexists _; iexact TTL
      isplitr
      · iexists _; iexact Error
      iexists log
      iunfold apply.grantHdr
      isplitl [Hhf]
      · iunfold txn.respHdrOwn
        iexists h
        iframe Header
        isplitr
        · ipureintro; exact Hh
        iunfold apply.hdrFields at Hhf
        iexact Hhf
      iexists h, _
      iframe Header Hrev Hnx
      ipureintro
      refine ⟨?_, Hlen.1, Hlen.2⟩
      word
    iexists 0, l
    iframe Hlf
    iexact Hreq

end proof

end EtcdGrove
end Perennial
