/-
**`applyAll` on a snapshot payload** (2026-11-01, J8a-5, step 5e; `notes/snapshot-j8a-plan.md`):
`EtcdServer.applyAll.specSnap` over `applySnapshot.specSnap` and the no-op cases of the other
steps. Lean-first. `run`'s snapshot case uses it (J8b).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyAll
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applySnapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntries
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Backend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__snapshotIfNeededAndCompactRaftLog
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.VerifyBackendConsistency
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRecvFacts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyDefs
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetSnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapSendBranch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem EtcdServer.applyAll.wp_proofSnap
    (hASnap : EtcdServer.applySnapshot.specSnap (GF := GF) (hG := hG))
    (hAE : EtcdServer.applyEntries.specNil (GF := GF) (hG := hG))
    (hBk : EtcdServer.Backend.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hV : backend.VerifyBackendConsistency.spec (GF := GF) (hG := hG))
    (hSINC : EtcdServer.snapshotIfNeededAndCompactRaftLog.specNoop (GF := GF) (hG := hG))
    -- the merge branch, as `wp_proof`'s
    (hGT : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (hGS : raftpb.Message.GetSnapshot.spec (GF := GF) (hG := hG))
    (hGM : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (hGI : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (hCM : EtcdServer.createMergedSnapshotMessage.spec (GF := GF) (hG := hG))
    (hSMS : EtcdServer.sendMergedSnap.spec (GF := GF) (hG := hG))
    (hC : mvcc.store.Commit.spec (GF := GF) (hG := hG))
    (hSnap : backend.backend.Snapshot.spec (GF := GF) (hG := hG))
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyAll.specSnap (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr b ep ap es sn sv rac nc st ai at0 a t cs x A mst γs γp γnc w nid nk q γn rt n
    hai hi61 hboot hAL hcia hraft hc0 hch hlog0 hcmp hγn hnI
  wp_start as ⟨#Hsrv, #Hsa, #Hnid, #Hes, #Hesl, #Hsnf, Hsnv, ⟨#Hcert, #Hsloc⟩, #Hncf, #Hnc2, Hnr0,
    #Hracf, #Hracc, #Hrtf, #Hrt, Hai, Hat, Hcs, Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, HKV, Hao, #Hlog,
    #HW, HWA, Hka, HRS, HAR, #Hkv, HwalT, Hso, #HmetaSnap⟩
  ihave #Hsrv' := Hsrv
  iunfold isServer at Hsrv'
  icases Hsrv' with ⟨%Hρrd, -, ⟨%fv, #Hfl⟩, #Hatm, -, #HrnS, -⟩
  iunfold srvFieldsAt at Hfl
  icases Hfl with ⟨#Hlgf, %Hlgnn, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, -⟩
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, ⟨%g, #Hg, #Hgs⟩, ⟨%bsl, #Hbsl⟩, -⟩
  ihave #Pbe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hatm' := Hatm
  iunfold srvAtomics at Hatm'
  icases Hatm' with ⟨#Hainv, -, #Hkvi⟩
  ihave #Hkvi2 := Hkvi
  iunfold srvKVInvs at Hkvi2
  icases Hkvi2 with ⟨-, -, #Hrli, -⟩
  -- the snapshot path's resources: the bundle, the counter, the backend's own
  iunfold srvSnapOwn at Hso
  icases Hso with ⟨%γt, %nt, #Hro, %Hnt, Hγt, Hsres⟩
  ihave #Hro' := Hro
  iunfold srvSnapRO at Hro'
  icases Hro' with ⟨%cfg, %ss, %hk, %lgh, %stp, %γd, %idm, %al, %ast, %lp, %cl, %ps, %dir, %d,
    %Hp, #Hcflg, #Hcfdd, #Hcffg, #Hfg, #Hcfq, #Hcfw, #Hssf, #Hssi, #Hhkf, #Hhk, #Hstp, #Hidm,
    #Hdinv, #Half, #Hauf, #Hlpf, #Hclf, #Hal, #HalOk, #HauOk, #HauR, #HlpOk, #HlpCfg, #HlpL, #Hrc,
    #HclOk, #Hvc, #Hmd, #Hks, #HlpI, #Hws, #Hcfg⟩
  obtain ⟨hkb, hlg, hstp, hdbo, hmm, hbuq, hsl, hdirps, hsop, hcm, hbr, hci, hhk, hwf, hlim, hlp,
    halbi, hwq, hRO, hrb⟩ := Hp
  icombine Hnid Hidm gives %Hidn
  subst Hidn
  -- the snapshot saved in the member's directory (`nodeSnapLocal` at the cluster's directories,
  -- the members')
  ihave #Hcok := Hrli
  iunfold srvRaftLogInv at Hcok
  icases Hcok with ⟨-, #Hcok, -⟩
  iunfold srvClusterOk at Hcok
  icases Hcok with ⟨-, -, -, -, -, -, -, %Hsloc'⟩
  ihave #Hsaved : snapSaved γd sv.Metadata'.Index' $$ []
  · iunfold snapSaved
    letI := srvStor (GF := GF) γr.raft.raft
    iapply (nodeSnapLocal_elem γr.raft.raft.cl nid γd (by rw [Hsloc'.1]; exact hsl))
    iexact Hsloc
  -- the snapshot's file out of the directory, the counter raised to its index (`snapDir_take`)
  have hnt' : nt < uint.nat sv.Metadata'.Index' := by
    have : uint.nat ai < uint.nat sv.Metadata'.Index' := by word
    omega
  wp_auto_lc 1
  imod snapDir_take ss γd γt γr (srvImage γr.raft.raft) sv.Metadata'.Index' ai nt hnt' hai
    $$ Hlc1 Hdinv Hsaved Hγt Hao with ⟨Hγt, Hao, %D, Hfile, #Himg⟩
  -- the image's facts (`snapRecv_image`): its committed log `A'` extending `A`
  have hai0 : uint.Z ai = uint.Z γr.raft.ai0 + A.length := by
    rw [hraft]; have := hAL; word
  imod snapRecv_image γr.raft.raft γr E sv.Metadata'.Index' ai D d A x cl _ hraft hc0 hch hlog0
      hai0 hai hboot hRO $$ Hkvi Himg Hka HRS Hrc with ⟨Hka, HRS, %A', %R, #HA', %Hif⟩
  -- the auth mode off (the run's), the KV's ghost state jumps to the image's log
  imod authOn_false_of_off s γ ci TM E ρ γr ρ.wait x A $$ [$Hsrv $HKV $Hka] with ⟨%Hoff, HKV, Hka⟩
  have hoff := authMode_off_of E Hoff
  imod snapRecv_kv_jump E γr A A' x Hif.pre Hif.hlen $$ Hkvi Hka HA' with ⟨%Hxch, #Hcert', HkaL⟩
  ihave #HcertK : mvcc.certOk E.γ ([[], []] ++ R) $$ []
  · rw [Hif.log]; iexact Hcert'
  obtain ⟨tI, hmeta⟩ := Hif.hmetaI
  -- the backend's own resources
  iunfold srvSnapRes at Hsres
  icases Hsres with ⟨%d0, %al0, %dd, %Hkb0, Hstopc, Hbo, #Hal0, HKC, #Hdd, Hpath⟩
  rw [hkb] at Hkb0
  cases Hkb0
  icombine Half Hal0 gives %Hale
  subst Hale
  icombine Hcfdd Hdd gives %Hdde
  subst Hdde
  have hncm : ¬ mvcc.kbCmpM E.γ.kb := by
    rw [hkb]; simp only [mvcc.kbCmpM]; rw [hcm, hcmp]; simp
  ihave HKC : srvKVCloser s E $$ [HKC]
  · rw [← srvKVCloserW_off s E hncm]; iexact HKC
  -- the apply thread's membership resources: the transport, the members' directory
  iunfold srvApRes at HAR
  icases HAR with ⟨%bh, %ix, %lgh', %tl, %lid, %cl', %lgc, %cid, %prs, #Hbhf, #Hbh, #Htrf, #Hmidf,
    #Hclf', #Hlgcf, %Hlgcnn, #Hcidf, Hmr, %Hpc, #Hdl⟩
  icombine Hclf Hclf' gives %Hcle
  subst Hcle
  icombine Hidm Hmidf gives %Hlide
  subst Hlide
  iunfold ccMembRes at Hmr
  icases Hmr with ⟨#Hrc', %γN, %c, %ps', %Hcl, Htlive, #Hmd', %Hdk⟩
  -- the snapshot state's indices
  iunfold srvSnapState at Hss
  icases Hss with ⟨%sd0, %sm0, %sf0, Hsd0, Hsm0, Hsf0, %Hdm0, #Hmst, #Hslb0⟩
  -- the configuration, rebuilt over `isServerApplyAll`'s two fields
  ihave #Hsa' := Hsa
  iunfold isServerApplyAll at Hsa'
  icases Hsa' with ⟨%wt, %msc, %sc, #Hwtf, #Hwt, #Hmscf, ⟨%γm, %Hγm, #Hmscb⟩, #Hscf,
    ⟨%stg, #Hstgf, #Hstgc⟩, ⟨%scu, #Hscuf⟩, #Hinf, -,
    ⟨%tr, %γNt, %lidt, %SN, %TSN, #Htrf2, #Htr, %HγNt⟩, %Hkv0⟩
  ihave #Hcfg' := Hcfg $$ %sc %scu Hscf Hscuf
  -- `s.applySnapshot(ep, apply)`, (2026-11-02, the backend-auth-split stage) with the apply
  -- thread's token (`srvGoRes`'s)
  iunfold srvGoRes at Hgr
  icases Hgr with ⟨HgrW, HthT⟩
  wp_apply (hASnap s ep ap sn sv γ ci TM E ρ γr ai at0 sd0 nc
      { cfg with SnapshotCount' := sc, SnapshotCatchUpEntries' := scu } ss hk hai d D lgh hkb
      (by rw [hcm, hcmp]) hdbo hsop ⟨hwf, hlim, hci, hhk⟩ hlg hmm tI hmeta st b (by omega)
      al ast lp cl x A hRO Hif.hlease hwq R Hif.hpre Hif.hRok Hif.hkI hbr hlp γp hrb stp γd γt
      (srvImage γr.raft.raft) (uint.nat sv.Metadata'.Index') hstp (Nat.le_refl _) Hif.halarm halbi
      Hif.hauthb Hif.hmemb _ Hif.himg γN tl c prs γN.dir ps' _ rfl Hdk.1 Hdk.2.1 Hcl sm0 cs
      cfg.ServerFeatureGate' cfg.QuotaBackendBytes' cfg.WarningApplyDuration' hbuq A' Hif.hA' hoff
      γnc)
    $$ [Hsnv Hnr0 Hai Hat Hsd0 Hlr Hbr Hfile Hpath Hst Hbe HKV HRS HKC Hγt Htlive Hsm0 Hcs Hstopc
      Hbo HthT]
    as ⟨Hsapp, Hnr1, HthT⟩
  · iframe #; iframe
    isplitr
    · iapply HauR; ipureintro; exact hoff
    rw [authApplyOk_eq, ← hoff]; iexact HauOk
  (try wp_auto)
  ihave Hgr : srvGoRes s $$ [HgrW HthT]
  · iunfold srvGoRes; iframe HgrW HthT
  iunfold srvSnapApplied at Hsapp
  icases Hsapp with ⟨%γ', %TM', %E', %b', %st', %d', %x', %cs', %L, %Hsa1, #Hsrv1, Hai, Hat, Hsd,
    Hsm, Hcs, #Hcso, Hst, Hbe, Hlr, Hbr, HKV, HRS, HKC, Hstopc, Hbo, Hγt, Hpath, Htlive,
    ⟨%kv', #Hkvf', #Hkvi'⟩⟩
  obtain ⟨hbs, hkb', hcm', hP', hRO', hlo', hci', hxl, hxch, hL⟩ := Hsa1
  -- `s.applyEntries(ep, apply)`: no entries
  wp_apply hAE s ep ap es $$ []
  · iframe #
  (try wp_auto)
  -- `backend.VerifyBackendConsistency(s.Backend(), s.Logger(), true, schema.AllBuckets...)`
  wp_apply hBk s E.γbe $$ [Hbr] as %be ⟨Hbr, -⟩
  · iframe #; iframe Hbr
  wp_apply hLg s fv.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hV be fv.lg true bsl
  (try wp_auto)
  -- `proposalsApplied.Set(float64(ep.appliedi))`
  iunfold gaugeSetSpec at Hgs
  wp_apply Hgs
  (try wp_auto)
  -- `s.applyWait.Trigger(ep.appliedi)`: the applied index jumps to the snapshot's (`applied_jump`)
  ihave #Hsrv1' := Hsrv1
  iunfold isServer at Hsrv1'
  icases Hsrv1' with ⟨-, -, -, #Hatm1, -, -⟩
  iunfold srvAtomics at Hatm1
  icases Hatm1 with ⟨#Hainv1, -, -⟩
  icases srvApplyKV_idxCert s E' ρ.wait x' $$ HKV with ⟨HKV, #Hic⟩
  have hiL : uint.Z sv.Metadata'.Index' = uint.Z γr.raft.ai0 + A'.length := by
    rw [hraft]; have := Hif.len; word
  ihave #HkL : kvLogAt γr sv.Metadata'.Index' x'.log $$ []
  · iunfold kvLogAt; iexists A'; iframe HA'; ipureintro; exact ⟨hiL, by rw [hxl]; exact Hif.log⟩
  imod applied_jump s E' γr ai sv.Metadata'.Index' x.log x'.log hai (by rw [hxl]; exact Hif.hpre)
    $$ Hainv1 Hao Hlog HkL Hic with ⟨Hao, #Hlb, #Hlog1⟩
  iunfold isWaitTime at Hwt
  icases Hwt with ⟨%wi, %Hwi, -, #HTrig⟩
  subst Hwi
  wp_apply HTrig $$ []
  · iintro !>; iexact Hlb
  (try wp_auto)
  -- `<-apply.notifyc`: the payload's second receive
  wp_apply wp_notify2_receive2 γnc nc _ _ $$ [Hnr1] as ⟨Hnr2, -⟩
  · iframe Hnc2 Hnr1
  (try wp_auto)
  -- the post's facts: the KV at the image's log, the voters, the log's last term, the membership
  -- resource at `A'`, the snapshot path's resources at the new backend
  ihave Hka : kvApplied γr.raft γr.kv A' x' $$ [HkaL]
  · iapply kvApplied_of_jump γr.raft γr.kv A' x' (by rw [hxl]; exact Hif.log)
      (by rw [hxch, Hoff, hch]) $$ HkaL
  have hpos : 0 < uint.Z sv.Metadata'.Index' := by have := hai; word
  have hρr : ρ.raft = γr.raft := by rw [← Hρrd]
  ihave #Hdl' := Hdl
  iunfold srvDynLog at Hdl'
  icases Hdl' with %Hlid
  imod epCsVoters_of_snap γr.raft sv cs' nid hpos hi61 Hlid $$ Hrli Hcert Hcso with #Hcv
  ihave #Hecs : epCsAt ρ.raft A' cs' $$ []
  · iunfold epCsAt; iright; rw [hρr]; iexact Hcv
  ihave %hltA := lastTermIs_of_snap γr.raft sv A' hpos hi61 (by rw [hraft]) Hif.len $$ Hrli Hcert HA'
  have hlenP : (γr.raft.pre ++ A').length = uint.nat sv.Metadata'.Index' := by
    rw [hraft]; simp only [List.nil_append]
    have := Hif.len; have := uint_nat_eq sv.Metadata'.Index'; omega
  ihave #Hkvi3 := Hkvi
  iunfold srvKVInvs at Hkvi3
  icases Hkvi3 with ⟨#Hkinv, -⟩
  imod kv_log_ccOk γr.raft γr.kv A' $$ Hkinv Hrli HA' with %Hcc
  have hmo : srvMemOk γr.raft γr.kv.c0 A' := by
    obtain ⟨B, hB⟩ := Hif.pre
    rw [← hB]
    exact srvMemOk_append _ _ A B Hpc.2
      (fun e he => Hcc e (by rw [← hB]; exact List.mem_append_right _ he))
  have hcov : srvPeersCover γr.raft nid A' L := fun f hf hne =>
    hL f ((netRh_member γN f).2 (Hdk.2.2 f hf)) hne
  ihave HAR' : srvApRes s γr A' $$ [Htlive]
  · iunfold srvApRes
    iexists bh, ix, lgh', tl, nid, cl, lgc, cid, L
    iframe Hbhf Hbh Htrf Hmidf Hclf' Hlgcf Hcidf Hdl
    isplitr
    · ipureintro; exact Hlgcnn
    isplitl [Htlive]
    · iunfold ccMembRes
      iframe Hrc'
      iexists γN, c, ps'
      iframe Htlive Hmd'
      ipureintro; exact ⟨Hcl, Hdk⟩
    ipureintro; exact ⟨hcov, hmo⟩
  ihave #Hro1 := srvSnapRO_succ s ci γr γt d d' al ast lp cl hbs hkb hkb' (by rw [hcm', hcmp]) hP'
    hRO' $$ [Hro Half Hauf Hlpf Hclf]
  · iframe Hro Half Hauf Hlpf Hclf
  have hncm' : ¬ mvcc.kbCmpM E'.γ.kb := by
    rw [hkb']; simp only [mvcc.kbCmpM]; rw [hcm']; simp
  ihave Hso' : srvSnapOwn s ci E' γr sv.Metadata'.Index' $$ [Hγt Hstopc Hbo HKC Hpath]
  · iunfold srvSnapOwn
    iexists γt, uint.nat sv.Metadata'.Index'
    iframe Hro1 Hγt
    isplitr
    · ipureintro; exact Nat.le_refl _
    iunfold srvSnapRes
    iexists d', al, cfg.DataDir'
    iframe Hstopc Hbo Half Hcfdd Hpath
    isplitr
    · ipureintro; exact hkb'
    rw [srvKVCloserW_off s E' hncm']; iexact HKC
  iunfold epConfState at Hcs
  icases Hcs with ⟨Hcs, #Hcsok⟩
  -- the step's end, shared by the selects' branches: the apply thread at a state `stF` of the
  -- same consistent index
  ihave Hfin : iprop(∀ stF : ApplyState, ⌜loopOk γ' stF sv.Metadata'.Index' ∧
        ciEff γ' stF.k = sv.Metadata'.Index'⌝ -∗
      epAppliedIAddr ep ↦ sv.Metadata'.Index' -∗ epAppliedTAddr ep ↦ sv.Metadata'.Term' -∗
      epConfStateAddr ep ↦ cs' -∗ srvSnapState s ep mst γs sv.Metadata'.Index' (W64 0) -∗
      applyThread γ' stF -∗ applyBackend γ' ci b' -∗ ciApplying ci a t -∗ srvLgReader s -∗
      srvGoRes s -∗ srvApplyKV s E' ρ.wait x' -∗ kvApplied γr.raft γr.kv A' x' -∗
      srvRest E' γr A' -∗ Φ #()) $$ [HΦ Hbr HAR' Hao HWA HwalT Hso']
  · iintro %stF %HF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr HKV Hka HRS
    ihave Hcs : epConfState ep cs' $$ [Hcs]
    · iunfold epConfState; iframe Hcs Hcsok
    iapply HΦ
    iexists γ', TM', E', b', stF, A', cs'
    isplitr
    · ipureintro; exact hbs
    iframe Hsrv1 HAR' HA' Hai Hat Hcs Hecs Hss Hst Hbe Happ Hlr Hgr Hbr Hao Hlb HWA HwalT Hso'
    isplitl [HKV Hka HRS]
    · iexists x'; iframe HKV Hlog1 Hka HRS
    isplitr
    · iexists kv'; iframe Hkvf' Hkvi'
    ipureintro; exact ⟨HF.1, HF.2, Hif.pre, hlenP, hltA⟩
  -- `select { case <-apply.raftAdvancedC: case <-s.stopping: return }`
  iunfold rnAdvChan at Hracc
  icases Hracc with ⟨%γac, #Hracc⟩
  ihave #HstgS := Hstgc
  iunfold stopChan at Hstgc
  icases Hstgc with ⟨%γsg, #Hstgc⟩
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  rotate_left
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stg, γsg
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownStopChan_is_chan $$ Hstgc
      iapply stop_chan_receive _ _ _ _ _ $$ Hstgc
      iintro ⟨-, -⟩
      (try wp_auto)
      ihave Hss : srvSnapState s ep mst γs sv.Metadata'.Index' (W64 0) $$ [Hsd Hsm Hsf0]
      · iunfold srvSnapState; iexists _, _, _; iframe Hsd Hsm Hsf0 Hmst Hslb0
        ipureintro; constructor <;> word
      have hF : loopOk γ' st' sv.Metadata'.Index' ∧ ciEff γ' st'.k = sv.Metadata'.Index' :=
        ⟨hlo', hci'⟩
      iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr HKV Hka HRS
    iapply BigAndL.bigAndL_nil.2
    itrivial
  ileft
  simp only [chan.blockingClausePre]
  iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, rac, γac
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply ownStopChan_is_chan $$ Hracc
  iapply stop_chan_receive _ _ _ _ _ $$ Hracc
  iintro ⟨-, -⟩
  (try wp_auto)
  -- `s.snapshotIfNeededAndCompactRaftLog(ep)`: nothing to do at the snapshot's index
  ihave Hfs : srvFS s $$ [Hsf0]
  · iunfold srvFS; iexists _; iexact Hsf0
  wp_apply hSINC s γr ep sv.Metadata'.Index' (by word) $$ [Hfs Hai Hsd Hsm]
    as ⟨Hfs, Hai, Hsd, Hsm⟩
  · iframe #; iframe
  (try wp_auto)
  iunfold srvFS at Hfs
  icases Hfs with ⟨%sf1, Hsf1⟩
  ihave Hss : srvSnapState s ep mst γs sv.Metadata'.Index' (W64 0) $$ [Hsd Hsm Hsf1]
  · iunfold srvSnapState; iexists _, _, _; iframe Hsd Hsm Hsf1 Hmst Hslb0
    ipureintro; constructor <;> word
  -- `select { case m := <-s.r.msgSnapC: ...; default: }`, as `wp_proof`'s at the snapshot's index
  have hF : loopOk γ' st' sv.Metadata'.Index' ∧ ciEff γ' st'.k = sv.Metadata'.Index' := ⟨hlo', hci'⟩
  have hlenZ : uint.Z sv.Metadata'.Index' = (A'.length : Int) := Hif.len
  iunfold isRNMsgSnapC at Hmscb
  icases Hmscb with ⟨%γc, #Hmscb⟩
  ihave #Hmscch := is_bag_is_chan γc msc _ $$ Hmscb
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.nonblockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, msc, γc
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact Hmscch
      unfold nonblockingRecvAu
      isplit
      · iapply chanBag_nbRecv γc msc _ _ $$ Hmscb
        iintro %m HP
        iunfold rnSnapMsg at HP
        icases HP with ⟨%sm, Hm, %Hty, #Hsm, -⟩
        rw [Hγm]
        letI := srvStor (GF := GF) γr.raft.raft
        ihave %Hsh := sentMsg_shape _ _ _ _ $$ Hsm
        obtain ⟨sn, hsn, -⟩ := Hsh.2 Hty
        ihave %Hsnp := srv_sentSnap_pos γr γm.id sm sn Hty hsn $$ [Hrli Hsm]
        · iframe Hrli Hsm
        -- two Go steps' time receipts (`m`'s zero value, `GetTerm`'s method value), for the merge
        -- window's write tokens
        repeat (
          fail_if_success wp_bind (App (Val (GoInstruction _)) (Val _))
          wp_pure)
        wp_bind (App (Val (GoInstruction _)) (Val _))
        iapply wp_go_step_receipt'
        case hv => first | rfl | simp [val.isPanic]
        inext
        iintro Hr1 -
        iapply wp_value'
        repeat (
          fail_if_success wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
          first | wp_pure | wp_load | wp_store | wp_alloc_auto)
        wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
        iapply wp_go_step_receipt'
        case hv => first | rfl | simp [val.isPanic]
        inext
        iintro Hr2 -
        iapply wp_value'
        (try wp_auto)
        wp_apply (hGT.1 m (DFrac.own 1) DFrac.discard false sm) $$ [Hm] as Hm
        · iframe #; iframe Hm
        (try wp_auto)
        wp_if_destruct
        · -- the batch's term: the snapshot's index
          wp_apply (hGS.1 m (DFrac.own 1) DFrac.discard false sm) $$ [Hm] as %ps ⟨Hsn, Hmb⟩
          · iframe #; iframe Hm
          rw [hsn]
          iunfold snapOpt at Hsn
          wp_apply (hGM.1 ps (DFrac.own 1) sn) $$ [Hsn] as %pm ⟨Hmd, Hsnb⟩
          · iframe #; iframe Hsn
          wp_apply (hGI pm (DFrac.own 1) sn.Metadata') $$ [Hmd] as Hmd
          · iframe #; iframe Hmd
          ihave Hsn := Hsnb $$ Hmd
          ihave Hm := Hmb $$ [Hsn]
          · iunfold snapOpt; iexact Hsn
          (try wp_auto)
          wp_if_destruct
          · -- the merge: the snapshot at most the applied index (the guard)
            (try wp_auto)
            -- (S2's `mergedCreate_window`) the commit's and the snapshot's contracts
            ihave #HsrvM : isServerM false s γ' ci TM' E' ρ γr $$ []
            · rw [isServerM_false]; iexact Hsrv1
            ihave #HW' : srvWTPool E' γp $$ []
            · obtain ⟨-, p, P, f, cc, RO, RW, hE⟩ := hbs
              rw [hE]
              iunfold srvWTPool at HW
              unfold srvWTPool
              rw [show (E.onBe p P f cc RO RW).γbe = E.γbe from rfl]
              iexact HW
            icases srvApplyKV_core s E' ρ.wait x' $$ HKV with ⟨%ua, HKVc, HKVk⟩
            imod mergedCreate_window hC hSnap hOn hSave hPut hUR hID hName hSafe false s γ' ci TM' E'
                ρ γr b' st' sv.Metadata'.Index' a t A' x' ρ.wait γp ua kv' hlo' hci' hpos hlenZ
              $$ [Hst Hbe Happ HKVc HRS Hr1 Hr2]
              with ⟨%be, %dq, %RC, %RC', %RS, %RS', Hkc, HRC, Hbeo, Hbs, HRCS, Hback⟩
            · iframe Hpkg HsrvM Hkvf' Hkvi' HW' Hlog1 HA' Hr1 Hr2 Hst Hbe Happ HKVc HRS
            wp_apply (hCM s m sm sv.Metadata'.Term' sv.Metadata'.Index' cs' fv.lg kv' be dq RC RC'
                RS RS' (mergedObs γr E'.cmp sv.Metadata'.Index' A' x'.log))
              $$ [Hlr Hkc HRC Hbeo Hbs HRCS Hm]
              as %mg ⟨Hlr, HRS', Hbeo, %rc, %Dm, %cm, #Hmg, #Hml, #Hcsom, Hrs, %HQd⟩
            · iframe #; iframe Hlr Hkc HRC Hbeo Hbs HRCS Hm; ipureintro; exact Hlgnn
            imod Hback $$ HRS' Hbeo with ⟨%st3, Hst, Hbe, Happ, HKVc, HRS, %Hst3⟩
            ihave HKV := HKVk $$ HKVc
            -- the merged message sent: of a term committed through the applied index (the batch's
            -- term, `rnRtOk`; not `0`, a `MsgSnap`'s term), certified at the voters' conf state
            iunfold rnRtOk at Hrt
            rw [hγn]
            icases Hrt with (%Hrt0 | ⟨%ct, #Hct, %Hnct⟩)
            · exfalso
              exact (Hsh.1.2.2.2.1 (by rw [Hty]; simp [MsgSnap, MsgProp, MsgReadIndex,
                MsgTransferLeader])) Hrt0
            ihave #Hcv2 := Hcv
            iunfold epCsVoters at Hcv2
            icases Hcv2 with ⟨%c0, #Hc0, %Hcs0⟩
            ihave %Hcc := csOpt_agree cs' cm c0 $$ [Hcsom Hc0]
            · iframe Hcsom Hc0
            subst Hcc
            imod srv_merged_sent γr A' sv.Metadata'.Index' sv.Metadata'.Term' cm γm.id ct sm sn hpos
                hi61 hmo.2 hlenZ hltA Hcs0 Hty hsn (by word)
                (by have := hnI; have := uint_nat_eq sv.Metadata'.Index'; omega)
              $$ [Hrli HA' Hsm Hct] with #Hsm'
            · iframe Hrli HA' Hsm Hct
            -- (S2's `merged_image`) the image's certificate
            imod merged_image s γ' ci TM' E' ρ γr sv.Metadata'.Index' A' x' Dm hlenZ ⟨hc0, hlog0⟩
              $$ [Hka] with ⟨Hka, #Himg'⟩
            · iframe Hsrv1 Hka; ipureintro; exact HQd
            imod srvMerged_bundle γr.raft.raft m rc sm γm.id cm sv.Metadata'.Index'
                sv.Metadata'.Term' Dm Hty
              $$ [Hml Hsm' Hrs Himg'] with Hbun
            · iframe Hml Hsm' Hrs Himg'
            (try wp_auto)
            wp_apply (hSMS s mg m rc fv.lg fv.memberID stg tr γNt SN TSN lidt) $$ [Hgr Hlr Hbun]
              as ⟨Hgr, Hlr⟩
            · iframe #; iframe Hgr Hlr; rw [HγNt]; iframe Hbun; ipureintro; exact Hlgnn
            (try wp_auto)
            have hF3 : loopOk γ' st3 sv.Metadata'.Index' ∧ ciEff γ' st3.k = sv.Metadata'.Index' :=
              ⟨Hst3.1, by rw [Hst3.2]; exact hci'⟩
            iapply Hfin $$ %st3 %hF3 Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr HKV Hka HRS
          · (try wp_auto)
            iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr HKV Hka HRS
        · (try wp_auto)
          iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr HKV Hka HRS
      · itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- `default`
    (try wp_auto)
    iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr HKV Hka HRS

end proof

end EtcdGrove
end Perennial
