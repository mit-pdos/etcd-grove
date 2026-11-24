/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedCluster__Finalize.lean` (claim #34,
stage 2, 2026-11-25), the first start (`!s.wal.haveWAL`, `bootstrap.go:512-527`): `SetID(c.nodeID,
c.cl.ID())` on the cluster not yet shared (`ID.specO`, `SetID`), `SetBackend` of a new membership
backend over the new backend whose membership buckets it creates (`SetBackend.specFresh`: the
backend's data becomes `bootGo.withMemBkts D`, the readers' view and compaction keys unchanged,
`BootFinalize.lean`), then the cluster's lock made (`rcLockInv_boot`, `sync.init_Mutex`: half the
members to the lock, the other half the apply thread's `clusterMem`; the local id read-only, a peer
by `bootGo.membersOk`; the members at most `2^62`, by `bootGo.initMapOk`), `Members()` under it and
`ValidateMaxLearnerConfig`. The rows `Hmembers`/`Hisc` come from the law `bootClusterRows.spec`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedCluster__Finalize
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootClusterRows
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__ID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__SetID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__SetBackend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Members
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__IsIDRemoved
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.ValidateMaxLearnerConfig
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.NewMembershipBackend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootFinalize

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem bootstrappedCluster.Finalize.wp_proof
    (hID : membership.RaftCluster.ID.specO (GF := GF) (hG := hG))
    (hSetID : membership.RaftCluster.SetID.spec (GF := GF) (hG := hG))
    (hNMB : schema.NewMembershipBackend.spec (GF := GF) (hG := hG))
    (hSB : membership.RaftCluster.SetBackend.specFresh (GF := GF) (hG := hG))
    (hMembers : membership.RaftCluster.Members.spec (GF := GF) (hG := hG))
    (hVMLC : membership.ValidateMaxLearnerConfig.spec (GF := GF) (hG := hG))
    (hIIR : membership.RaftCluster.IsIDRemoved.spec (GF := GF) (hG := hG))
    (hRows : bootClusterRows.spec (GF := GF) (hG := hG)) :
    bootstrappedCluster.Finalize.spec (GF := GF) (hG := hG) := by
  intro cfg U c s bc sto bk bw d W Pk N D dq dqs dqb dqw Hok HiOk Hid Hhw Hbe Hm Hmr Hcl
  wp_start as ⟨#Hzlg, Hc, Hs, Hbk, Hbw, Hcb, Hnew, Hwbt⟩
  ihave %Hlgnn := zapLoggerOk_ne_null $$ Hzlg
  iunfold clusterBuilt at Hcb
  icases Hcb with ⟨%ms, %lgc, %rp, %dp, Hclg, #Hlgok, Hlid, Hcid, Hcbe, Hmu, Hver, Hmem0, Hrm,
    Hrmm, -, -, -, Hvc⟩
  ihave #Hmpkg : isPkgInit (PROP := IProp GF)
    pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  -- the members map's domain, for the lock's bound and the local member
  iunfold membership.memAt at Hmem0
  icases Hmem0 with ⟨%mp0, Hf0, Hm0, %Hdom, Hb0⟩
  ihave Hmem0 : membership.memAt (GF := GF) bc.cl' 1 ms (bootGo.memMap U cfg.InitialClusterToken')
    $$ [Hf0 Hm0 Hb0]
  · iunfold membership.memAt
    iexists mp0
    isplitl [Hf0]
    · iexact Hf0
    isplitl [Hm0]
    · iexact Hm0
    isplitr
    · ipureintro; exact Hdom
    iexact Hb0
  have hsz : GMap.size ms ≤ 2 ^ 62 := by
    have h1 := Hdom.2
    have h2 := bootGo.memMap_size_le U cfg.InitialClusterToken'
    have h3 := HiOk.2
    omega
  have hin : ms !! bc.nodeID' ≠ none := by
    have h1 := (bootGo.memMap_isSome U cfg.InitialClusterToken' bc.nodeID').2
      (by rw [Hid]; exact Hok.2.2.2)
    have h2 := Hdom.1 bc.nodeID'
    rw [← h2] at h1
    intro h
    rw [h] at h1
    simp at h1
  wp_auto
  -- `if !s.wal.haveWAL { c.cl.SetID(c.nodeID, c.cl.ID()) }`
  rw [Hhw]
  wp_auto
  wp_apply (hID bc.cl' (DFrac.own 1) _) $$ [$Hmpkg $Hcid] as Hcid
  icases membership.memAt_open bc.cl' 1 ms _ $$ Hmem0 with ⟨%mp, Hmf, Hmp, Hmems, Hmcl⟩
  wp_apply (hSetID bc.cl' bc.nodeID' (bootGo.cid U cfg.InitialClusterToken') (W64 0) _
      (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) mp rp ms ∅)
    $$ [$Hmpkg $Hlid $Hcid $Hmf $Hmp $Hrm $Hrmm] as ⟨Hlid, Hcid, Hmf, Hmp, Hrm, Hrmm⟩
  ihave Hmem0 := Hmcl $$ Hmf Hmp Hmems
  (try wp_auto)
  -- `c.cl.SetBackend(schema.NewMembershipBackend(cfg.Logger, s.backend.be))`
  wp_apply (hNMB cfg.Logger' bk.be') $$ [$Hspkg] as %mbl ⟨#Hmblg, #Hmblb⟩
  ihave #Hmblb' : (structFieldRef go_etcd_io.etcd.server.v3.storage.schema.membershipBackend go!"be"
      mbl ↦□ (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
        #d.be : GoInterface) : IProp GF) $$ []
  · rw [← Hbe]; iexact Hmblb
  iunfold backend.newPostK at Hnew
  icases Hnew with ⟨#HB, #HSC, HK, HV, HH, HRB, HRd, HDl, HFk, HSr, HTok⟩
  iunfold bootLeft at HK
  icases HK with ⟨Htoks, Ho⟩
  iunfold backend.rbOwn at HRB
  (try wp_auto)
  wp_apply (hSB bc.cl' GoInterface.nil mbl cfg.Logger' d (W d.γB) (Pk d.γB) 1 (fun _ => True)
      (backend.rbData d.P D) (fun _ _ => trivial) Hm Hmr Hcl)
    $$ [$Hmpkg $Hspkg $Hcbe $Hmblb' $Hmblg $HB $Ho $Hwbt $HRB] as ⟨HclBe, Ho, HRB⟩
  · ipureintro; exact Hlgnn
  (try wp_auto)
  -- the cluster's lock, from its fields (it is not shared before)
  ipersist Hlid
  ipersist Hcid
  ipersist Hclg
  icases membership.memAt_halve bc.cl' ms _ $$ Hmem0 with ⟨HmemL, HmemA⟩
  imod membership.rcLockInv_boot bc.cl' ms _ rp hsz $$ [HmemL Hrm Hrmm Hver] with ⟨%γcv, Hinv⟩
  · isplitl [HmemL]
    · iexact HmemL
    isplitr
    · iunfold membership.rcLocalIn
      iexists bc.nodeID'
      isplitr
      · iexact Hlid
      ipureintro; exact hin
    isplitl [Hrm]
    · iexact Hrm
    isplitl [Hrmm]
    · iexact Hrmm
    iexact Hver
  imod sync.init_Mutex (membership.rcLockInv (GF := GF) bc.cl' γcv) ⊤ (membership.rcMutexAddr bc.cl')
    $$ Hmu [Hinv] with #Hmtx
  · inext; iexact Hinv
  ihave #Hrc : membership.isRaftCluster (GF := GF) bc.cl' $$ []
  · iunfold membership.isRaftCluster
    iexists γcv
    iunfold membership.isRaftClusterV
    iexact Hmtx
  -- `membership.ValidateMaxLearnerConfig(cfg.MaxLearners, c.cl.Members(), false)`
  wp_apply (membership.RaftCluster.Members.spec_static hMembers bc.cl') $$ [$Hmpkg $Hrc]
    as %sl ⟨%mls, Hmls⟩
  (try wp_auto)
  wp_apply (hVMLC _ sl mls _) $$ [$Hmpkg $Hmls] as %err -
  (try wp_auto)
  iapply HΦ
  isplitl [Hc]
  · iexact Hc
  isplitl [Hs]
  · iexact Hs
  isplitl [Hbk]
  · iexact Hbk
  isplitl [Hbw]
  · iexact Hbw
  isplitl [Htoks Ho HV HH HRB HRd HDl HFk HSr HTok]
  · iunfold backend.newPostK
    isplitr
    · iexact HB
    isplitr
    · iexact HSC
    isplitl [Htoks Ho]
    · iunfold bootLeft
      isplitl [Htoks]
      · iexact Htoks
      iexact Ho
    isplitl [HV]
    · rw [bootGo.vData_withMemBkts]; iexact HV
    isplitl [HH]
    · iexact HH
    isplitl [HRB]
    · iunfold backend.rbOwn
      iapply (backend.rbPart_congr d.γB (fun _ => True)
        (backend.rbData d.P (bootGo.withMemBkts D)) (schema.withMemBkts (backend.rbData d.P D))
        (fun n _ => bootGo.rbData_withMemBkts d D n)).2
      iunfold backend.rbPart
      iexists (fun _ => false)
      iunfold backend.rbOwnIn at HRB
      iexact HRB
    isplitl [HRd]
    · iexact HRd
    isplitl [HDl]
    · iexact HDl
    isplitl [HFk]
    · rw [bootGo.fkCl_withMemBkts]; iexact HFk
    isplitl [HSr]
    · iexact HSr
    iexact HTok
  by_cases herr : err = GoInterface.nil
  · iright
    isplitr
    · ipureintro; exact herr
    ihave HcM : membership.clusterMem (GF := GF) bc.cl' (bootGo.memMap U cfg.InitialClusterToken')
      $$ [HmemA]
    · iunfold membership.clusterMem; iexists ms; iexact HmemA
    ihave #Hcc : membership.clusterCid (GF := GF) bc.cl' (bootGo.cid U cfg.InitialClusterToken') $$ []
    · iunfold membership.clusterCid; iexact Hcid
    icases (hRows cfg U bc.cl' Hok) $$ [HcM] with ⟨HcM, #Hmembers, #Hisc⟩
    · isplitr
      · iexact Hrc
      isplitr
      · iexact Hcc
      iexact HcM
    iunfold bootClusterDone
    isplitr
    · iunfold rnClusterOk
      imodintro
      iintro %id %Φ' - HΦ'
      wp_apply (membership.RaftCluster.IsIDRemoved.spec_static hIIR bc.cl' id) $$ [$Hmpkg $Hrc]
      iapply HΦ'
      itrivial
    isplitr
    · iexact Hrc
    isplitr
    · iexact Hcc
    isplitr
    · iexists lgc
      isplitr
      · iexact Hclg
      iexact Hlgok
    isplitl [Hvc]
    · iexists null; iexact Hvc
    isplitr
    · iexact Hmembers
    isplitr
    · iexact Hisc
    isplitl [HclBe]
    · iexact HclBe
    iexact HcM
  · ileft
    ipureintro; exact herr

end proof

end EtcdGrove
end Perennial
