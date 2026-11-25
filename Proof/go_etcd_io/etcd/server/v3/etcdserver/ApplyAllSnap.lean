/-
Proof of `applyAll`'s snapshot case, `EtcdServer.applyAll.specSnapM`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applyAll.lean`), in both auth modes and in
restart form. Lean-first (no Rocq counterpart).

(R2d'a swap batch 2, 2026-11-06; review F1, the swap the user approved) Until the swap this file held
the mode-off proof `wp_proofSnap` of `applyAll.specSnap`, `ApplyAllSnapOn.lean` the mode-generic
`wp_proofSnapM` over it, and `ApplyAllSnapR.lean` the restart form `specSnapMR` with its proof. The
restart form is now `specSnapM` and its proof `wp_proofSnapM` (generated from the two frozen proofs,
with the directory's file taken at the ghost index `g` (`snapDir_take`), the image's facts at `g` and
`r0` (`snapRecv_imageR`/`snapRecv_imageOnR`, `ApplyAllSnapLemmas.lean`), `applySnapshot.specSnapM` at Go's `ai` and `r0`,
and the ghost index's jump from `g` (`applied_jump(M)`)); the two frozen proofs are deleted.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyAllSnapLemmas

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
/-- **`applyAll.specSnapM`** (F9; P6.3; R2d'a task 4 and swap batch 2, 2026-11-06): both auth
modes, at the split index (until the swap two proofs, `wp_proofSnap` off and `wp_proofSnapM` on,
over the first-start statement). -/
theorem EtcdServer.applyAll.wp_proofSnapM
    (hASnap : EtcdServer.applySnapshot.specSnapM (GF := GF) (hG := hG))
    (hAE : EtcdServer.applyEntries.specNil (GF := GF) (hG := hG))
    (hBk : EtcdServer.Backend.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hV : backend.VerifyBackendConsistency.spec (GF := GF) (hG := hG))
    (hSINC : EtcdServer.snapshotIfNeededAndCompactRaftLog.specNoop (GF := GF) (hG := hG))
    -- the merge branch, as `wp_proofOn`'s
    (hGT : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (hCM : EtcdServer.createMergedSnapshotMessage.specCaughtUp (GF := GF) (hG := hG))
    (hSMS : EtcdServer.sendMergedSnap.spec (GF := GF) (hG := hG))
    (hGTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (hRSn : EtcdServer.ReportSnapshot.spec (GF := GF) (hG := hG))
    [mvccSem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hPers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hReach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hImg : mvcc.api.mvccImage_snapshot.law (GF := GF) (hG := hG))
    (hSnap : backend.backend.Snapshot.spec (GF := GF) (hG := hG))
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyAll.specSnapM (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr b ep ap es sn sv rac nc st ai at0 a t cs x A mst γs γp γnc w nid nk q γn rt n
    sa ag r0 hany hag hgi hi61 hboot hAL hcia hpd hids hraft hc0 hch hlog0 hγn hnI hbase hns
  have hai : uint.Z ai < uint.Z sv.Metadata'.Index' := by omega
  cases hM : E.authMode with
  | any => exact absurd hM hany
  | off =>
    have hon : E.authOn = false := by simp [apply.AEnv.authOn, hM]
    have hoffE : E.authMode = .off := hM
    rw [hon] at hch ⊢
    simp only [srvApplyKVM_false, kvAppliedM_false, isServerM_false, srvRestRpM_false, srvRestM_false]
    wp_start as ⟨#Hsrv, #Hsa, #Hnid, #Hes, #Hesl, #Hsnf, Hsnv, ⟨#Hcert, #Hsloc⟩, #Hncf, #Hnc2, Hnr0,
      #Hracf, #Hracc, #Hrtf, #HreplayField, #Hrt, #Hmerge, Hcursor, HbootField, Hai, Hat, Hcs, Hss, Hst, Hbe, Happ, Hlr, Hgr, Hrdk, Hbr, HKV, Hao, #Hlog,
      #HW, HWA, Hka, HRS, HAR, #Hkv, HwalT, Hso, #HmetaSnap⟩
    icases srvApRes_cfg_size s γr _ $$ HAR with ⟨HAR, %hsz20⟩
    ihave #Hsrv' := Hsrv
    iunfold isServer at Hsrv'
    icases Hsrv' with ⟨%Hρrd, -, ⟨%fv, #Hfl⟩, #Hatm, -, #HrnS, -⟩
    iunfold srvFieldsAt at Hfl
    icases Hfl with ⟨#Hlgf, #Hlgnn, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, -⟩
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
    icases Hkvi2 with ⟨#HkI0, -, #Hrli, -, %Hkvp, -⟩
    obtain ⟨-, -, ⟨hw1, hw2, hw3, hw4⟩, -⟩ := Hkvp
    -- (the auth-on pair's F8) the cluster runs auth off, the member's KV invariant says
    imod (kvInv_authOn γr.raft γr.kv) $$ HkI0 with %hao
    -- the snapshot path's resources: the bundle, the counter, the backend's own
    iunfold srvSnapOwn at Hso
    icases Hso with ⟨%γt, %nt, #Hro, %Hnt, Hγt, Hsres⟩
    ihave #Hro' := Hro
    iunfold srvSnapRO at Hro'
    icases Hro' with ⟨%cfg, %ss, %hk, %lgh, %stp, %γd, %idm, %al, %ast, %lp, %cl, %ps, %dir, %d,
      %Hp, #Hcflg, #Hcfzl, #Hcfdd, #Hcffg, #Hfg, #Hvoff, #Hcfq, #Hcfw, #Hssf, #Hssi, #Hhkf, #Hhk, #Hstp, #Hidm,
      #Hdinv, #Half, #Hauf, #Hlpf, #Hclf, #Hal, #HalOk, #HauOk, #HauR, #HauSK, #HlpOk, #HlpCfg, #Hrc,
      #HclOk, #Hvc, #Hmd, #Hks, #HlpI, #HlpM, ⟨#Hkvaddr, #Hkvm⟩, #Hcfg, #Hclgz, #Hsws⟩
    obtain ⟨hkb, hdbo, hmm, hbuq, hsl, hdirps, hsop, hbr, hci, hhk, hwf, hlim, hlp,
      halbi, hmbP, hRO, hrb, hdd⟩ := Hp
    -- (the lease-expiry plan's S2–S4 Probe, 2026-11-05: in either lease mode; until then the
    -- revocable lessor refuted the rest's leased arm, a cluster that grants none) the lessor at the
    -- environment's mode
    icases HlpM with ⟨%Hmo, #HlpE⟩
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
    -- the snapshot's file out of the directory, the counter raised to its index and sealed with it (`snapDir_take`, `snapRmM_take`)
    have hnt' : nt ≤ uint.nat sv.Metadata'.Index' := by
      have : uint.nat ag < uint.nat sv.Metadata'.Index' := by word  -- (route (C)) the ghost index
      omega
    wp_auto_lc 1
    ihave #Hdinv' : inv snapDirN (snapDirInv (config.snapDirOf cfg.DataDir') γd (srvImage γr.raft.raft) (snapRmM γt)) $$ []
    · rw [← srvImageM_off, ← hao]; iexact Hdinv
    ihave Htake := snapRmM_take (GF := GF) γt sv.Metadata'.Index' nt hnt'
    icases Htake with ⟨Hno, Hup⟩
    imod snapDir_take (config.snapDirOf cfg.DataDir') γd (srvImage γr.raft.raft) (snapRmM γt) sv.Metadata'.Index'
        (monoNatAuthOwn γt 1 nt) (monoNatAuthOwn γt 1 (uint.nat sv.Metadata'.Index' + 1))
        $$ Hlc1 Hdinv' Hsaved Hγt Hno Hup with ⟨%D, Hfile, #Himg⟩
    -- the image's facts (`snapRecv_image`): its committed log `A'` extending `A`
    have hai0 : uint.Z ag = uint.Z γr.raft.ai0 + A.length := by
      rw [hraft]; have := hAL; word
    imod snapRecv_imageR γr.raft.raft γr E sv.Metadata'.Index' ag D d A x cl _ hraft hc0 hch hlog0
        hai0 hgi hboot hRO r0 hids $$ Hkvi Himg Hka HRS Hrc
      with ⟨Hka, HRS, %A', %u, #HA', %Hif, #Him0, #HCp0⟩
    icases kvApplied_facts γr.raft γr.kv A x $$ Hka with ⟨Hka, %HxA⟩
    -- the auth mode off (the run's), the KV's ghost state jumps to the image's log
    imod authOn_false_of_off s γ ci TM E ρ γr ρ.wait x A $$ [$Hsrv $HKV $Hka] with ⟨%Hoff, HKV, Hka⟩
    have hoff := authMode_off_of E Hoff
    imod snapRecv_kv_jump E γr A A' x Hif.pre (by have := Hif.hst.2; omega) $$ Hkvi Hka HA'
      with ⟨%Hxch, HkaL⟩
    obtain ⟨tI, hmeta⟩ := Hif.hmetaI
    -- the backend's own resources
    iunfold srvSnapRes at Hsres
    icases Hsres with ⟨%d0, %al0, %dd, %Hkb0, Hstopc, Hbo, #Hal0, #Hdd, Hpath, -⟩
    obtain rfl := srvBkTie_inj d d0 (hkb.symm.trans Hkb0)
    icombine Half Hal0 gives %Hale
    subst Hale
    icombine Hcfdd Hdd gives %Hdde
    subst Hdde
    -- the apply thread's membership resources: the transport, the members' directory
    iunfold srvApRes at HAR
    icases HAR with ⟨%bh, %ix, %lgh', %tl, %lid, %cl', %lgc, %cid, %prs, #Hbhf, #Hbh, #Htrf, #Hmidf,
      #Hclf', #Hlgcf, #Hlgcnn, #Hcidf, Hmr, %Hpc, #Hdl⟩
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
    icases Hsa' with ⟨%wt, %msc, %sc, #Hwtf, #Hwt, #Hmscf, ⟨%γm, %Hγm, #Hmidm, -, #Hrnf, #Hrnsi⟩, #Hscf,
      ⟨%stg, #Hstgf, #Hstgc⟩, ⟨%scu, #Hscuf, -⟩, #Hinf, -,
      ⟨%tr, %γNt, %lidt, %SN, %TSN, #Htrf2, #Htr, %HγNt⟩, %Hkv0⟩
    ihave #Hcfg' := Hcfg $$ %sc %scu Hscf Hscuf
    -- `s.applySnapshot(ep, apply)`, (2026-11-02, the backend-auth-split stage) with the apply
    -- thread's token (`srvGoRes`'s)
    iunfold srvGoRes at Hgr
    icases Hgr with ⟨HgrW, HthT⟩
    -- (F9, 2026-11-03) `specSnapM` in the mode `off`: the auth store's `Recover` facts `authRecoverOk`
    ihave #HauS : snapAuthResM E.authMode s ast E.RD γr A' $$ []
    · rw [hoff]; simp only [snapAuthResM]; iapply HauR; ipureintro; first | trivial | rfl | exact hoff
    have hposS : 0 < uint.Z sv.Metadata'.Index' := by have := hai; word
    imod snap_csIdCount γr.raft sv hposS hi61 hsz20 $$ Hrli Hcert with %hcsz
    have hS := (hASnap s ep ap sn sv γ ci TM E ρ γr ai at0 sd0 nc
        { cfg with SnapshotCount' := sc, SnapshotCatchUpEntries' := scu } ss hk hai hcsz d D lgh hkb
        hdbo hsop ⟨hwf, hlim, hci, hhk⟩ hmm hdd tI hmeta st b (by omega) hpd
        al ast lp cl x A r0 hRO A' u (by rw [Hoff]; exact HxA) (by rw [Hoff]; exact Hif.hst)
        (by rw [Hoff]; exact Hif.nolease) hbr hlp γp
        hrb stp γd γt
        (srvImage γr.raft.raft) (uint.nat sv.Metadata'.Index' + 1) (Nat.le_refl _) Hif.halarm halbi hmbP
        Hif.hmemb _ Hif.himg γN tl c prs γN.dir ps' _ rfl Hdk.1 Hdk.2.1 Hcl sm0 cs
        cfg.ServerFeatureGate' cfg.QuotaBackendBytes' cfg.WarningApplyDuration' hbuq
        Hif.pre (by rw [Hoff]; exact Hif.hA') (by rw [Hoff, imageLeasesAtM_false]; exact Hif.hlease)
        (by rw [hraft]) Hmo (by rw [hoff]; simp) (by rw [hoff]; exact Hif.hauthb) γnc γn q hns)
    rw [Hoff] at hS
    simp only [srvApplyKVM_false, isServerM_false, srvSnapAppliedM, kvModelM_false, srvRestRpM_false] at hS
    wp_apply hS
      $$ [Hsnv Hnr0 Hai Hat Hsd0 Hlr Hbr Hfile Hpath Hst Hbe HKV HRS Htlive Hsm0 Hcs HbootField Hstopc
        Hbo HthT HwalT]
      as ⟨Hsapp, Hnr1, HthT, HbootField, HwalT⟩
    · iframe #; iframe
    (try wp_auto)
    ihave Hgr : srvGoRes s $$ [HgrW HthT]
    · iunfold srvGoRes; iframe HgrW HthT
    iunfold srvSnapApplied at Hsapp
    icases Hsapp with ⟨%γ', %TM', %E', %b', %st', %d', %x', %cs', %L, %Hsa1, #Hsrv1, Hai, Hat, Hsd,
      Hsm, Hcs, #Hcso, Hst, Hbe, Hlr, Hbr, HKV, HRS, Hstopc, Hbo, Hγt, Hpath, #Hbf', Htlive,
      ⟨%kv', #Hkvf', #Hkvi', %Hkve⟩⟩
    obtain ⟨hbs, hkb', hP', hRO', hlo', hci', hxl, hxcr, hxch, hL⟩ := Hsa1
    -- the apply thread's reader token, at the new environment's store (`beSucc` keeps it)
    ihave Hrdk : mvcc.api.mvccReaders (GF := GF) E'.γ 1 $$ [Hrdk]
    · iapply (show mvcc.api.mvccReaders (GF := GF) E.γ 1 ⊢ mvcc.api.mvccReaders E'.γ 1 by
        obtain ⟨-, _, _, _, _, _, _, hE⟩ := hbs; rw [hE]; exact .rfl)
      iexact Hrdk
    have hoff' : E'.authMode = auth.AuthMode.off := by
      obtain ⟨-, _, _, _, _, _, _, hE⟩ := hbs; rw [hE]; exact hoff
    -- `s.applyEntries(ep, apply)`: no entries
    wp_apply hAE s ep ap es $$ []
    · iframe #
    (try wp_auto)
    -- `backend.VerifyBackendConsistency(s.Backend(), s.Logger(), true, schema.AllBuckets...)`
    wp_apply hBk s E.γbe $$ [Hbr] as %be ⟨Hbr, %dB, -, #HbRO⟩
    · iframe #; iframe Hbr
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off, the backend's
    ihave #Hvoff := srvBeRO_etcdVerifyOff dB $$ HbRO
    wp_apply hLg s fv.lg $$ [Hlr] as ⟨-, Hlr⟩
    · iframe #; iframe Hlr
    (try wp_auto)
    wp_apply hV be fv.lg true bsl $$ []
    · iframe #
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
    icases Hatm1 with ⟨#Hainv1, -, #Hkvi1⟩
    imod srvApplyKV_writer hPers hReach s E' γr ρ.wait x' $$ Hkvi1 HKV with ⟨HKV, #Hic, -, -, -⟩
    have hiL : uint.Z sv.Metadata'.Index' = uint.Z γr.raft.ai0 + A'.length := by
      rw [hraft]; have := Hif.len; word
    ihave #HkL : kvLogAt γr sv.Metadata'.Index' x'.log $$ []
    · iunfold kvLogAt; iexists A'; iframe HA'; ipureintro; exact ⟨hiL, hxl⟩
    imod applied_jump s E' γr ag sv.Metadata'.Index' x.log x'.log hgi
        (by rw [hxl, HxA.1]; exact kvRaftOf_prefix _ _ _ _ _ Hif.pre)
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
    · iapply kvApplied_of_jump γr.raft γr.kv A' x' hxl
        (by rw [hxch, Hoff, hch]) hxcr $$ HkaL
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
      · iexact Hlgcnn
      isplitl [Htlive]
      · iunfold ccMembRes
        iframe Hrc'
        iexists γN, c, ps'
        iframe Htlive Hmd'
        ipureintro; exact ⟨Hcl, Hdk⟩
      ipureintro; exact ⟨hcov, hmo⟩
    ihave #Hro1 := srvSnapRO_succ s ci γr γt d d' al ast lp cl hbs hkb hkb' hP'
      hRO' $$ [Hro Half Hauf Hlpf Hclf]
    · iframe Hro Half Hauf Hlpf Hclf
    ihave Hbo : backend.bOpen (GF := GF) d'.γB (srvOpenQ E'.authMode) $$ [Hbo]
    · rw [hoff', srvOpenQ_off]; iexact Hbo
    -- MERGE-TODO(close): `lean`'s `srvSnapRes` also held the KV's closer (`HKC`)
    ihave Hso' : srvSnapOwn s ci E' γr γ' sv.Metadata'.Index' $$ [Hγt Hstopc Hbo Hpath]
    · iunfold srvSnapOwn
      iexists γt, uint.nat sv.Metadata'.Index' + 1
      iframe Hro1 Hγt
      isplitr
      · ipureintro; exact Nat.le_refl _
      iunfold srvSnapRes
      iexists d', al, cfg.DataDir'
      iframe Hstopc Hbo Half Hcfdd Hpath
      isplitr
      · ipureintro; exact hkb'
      iexact Hbf'
    iunfold epConfState at Hcs
    icases Hcs with ⟨Hcs, #Hcsok⟩
    -- the step's end, shared by the selects' branches: the apply thread at a state `stF` of the
    -- same consistent index
    ihave Hfin : iprop(∀ stF : ApplyState, ⌜loopOk γ' stF sv.Metadata'.Index' ∧
          ciEff γ' stF.k = sv.Metadata'.Index'⌝ -∗
        epAppliedIAddr ep ↦ sv.Metadata'.Index' -∗ epAppliedTAddr ep ↦ sv.Metadata'.Term' -∗
        epConfStateAddr ep ↦ cs' -∗ srvSnapState s ep mst γs sv.Metadata'.Index' (W64 0) -∗
        applyThread γ' stF -∗ applyBackend γ' ci b' -∗ ciApplying ci a t -∗ srvLgReader s -∗
        srvGoRes s -∗ mvcc.api.mvccReaders E'.γ 1 -∗ srvApplyKV s E' ρ.wait x' -∗
        kvApplied γr.raft γr.kv A' x' -∗
        srvRest E' γr A' -∗ monoNatAuthOwn γr.cursor 1 n -∗ epReplayConfAddr ep ↦ (null : Loc) -∗ srvAppliedOwn γr sv.Metadata'.Index' -∗ Φ #()) $$ [HΦ Hbr HAR' HWA HwalT Hso']
    · iintro %stF %HF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS Hcursor HbootField Hao
      ihave Hcs : epConfState ep cs' $$ [Hcs]
      · iunfold epConfState; iframe Hcs Hcsok
      iapply HΦ
      iexists γ', TM', E', b', stF, A', cs'
      iframe Hcursor HbootField
      isplitr
      · ipureintro; exact hbs
      iframe Hsrv1 HAR' HA' Hai Hat Hcs Hecs Hss Hst Hbe Happ Hlr Hgr Hrdk Hbr Hao Hlb HWA HwalT Hso'
      isplitl [HKV Hka HRS]
      · iexists x'; iframe HKV Hlog1 Hka HRS
      isplitr
      · iexists kv'; iframe Hkvf' Hkvi'; ipureintro; exact Hkve
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
        iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS Hcursor HbootField Hao
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
    iunfold srvMergeAttachment at Hmerge
    icases Hmerge with ⟨%srcChan, %pin, #Hcf, #Hmscb, #Hlocpin, #Htagpin⟩
    icombine Hmscf Hcf gives %hchan
    subst srcChan
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
          icases HP with ⟨%sm, Hm, %Hty, #Hsm, -, #Huf, #Hsrc⟩
          ihave %Hsh := (letI := srvStor (GF := GF) γn.node; sentMsg_shape γn.node.cl srvClusterN γn.id sm) $$ Hsm
          obtain ⟨sn, hsn, -⟩ := Hsh.2 Hty
          ihave Hidx := srv_merge_index γn γr pin ⟨m, sm⟩ sn rt n Hty hsn hbase
            $$ Hsrc Hrt Hsm Hlocpin Htagpin
          rw [hγn]
          letI := srvStor (GF := GF) γr.raft.raft
          ihave %Hsnp := srv_sentSnap_pos γr γn.id sm sn Hty hsn $$ [Hrli Hsm]
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
          iintro Hr1 Hl1
          iapply wp_value'
          repeat (
            fail_if_success wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
            first | wp_pure | wp_load | wp_store | wp_alloc_auto)
          wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
          iapply wp_go_step_receipt'
          case hv => first | rfl | simp [val.isPanic]
          inext
          iintro Hr2 Hl2
          iapply wp_value'
          (try wp_auto)
          wp_apply (hGT.1 m (DFrac.own 1) DFrac.discard false sm) $$ [Hm] as Hm
          · iframe #; iframe Hm
          (try wp_auto)
          wp_if_destruct
          · -- The message belongs to the term of this apply batch.
            ihave ⟨Hcursor, %hidxRaft⟩ := Hidx $$ %True.intro Hcursor
            (try wp_auto)
            -- Installing this snapshot already established the backend index at the apply cursor.
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
            -- the apply goroutine's token, lent to the commit
            ihave HthT : apply.applyTok (GF := GF) E' $$ [Hrdk]
            · iunfold apply.applyTok; iexact Hrdk
            have HE'off : E'.authOn = false := by unfold apply.AEnv.authOn; rw [hoff']; rfl
            ihave HRS : srvRestM E'.authOn E' γr A' $$ [HRS]
            · rw [HE'off, srvRestM_false]; iexact HRS
            imod mergedCreate_window hsh hPers hReach hImg hSnap hOn hSave hPut hUR hID hName hSafe false s
                γ' ci TM' E' ρ γr b' st' sv.Metadata'.Index' a t A' x' ρ.wait γp ua kv' hlo'
                (fun _ => False) (fun _ => True) emp (fun _ h => h.elim)
              $$ [Hst Hbe Happ HKVc HRS Hr1 Hl1 HthT]
              with ⟨%be, %dq, %RC, %RC', %RS, %RS', %Qd, Hkc, HRC, Hbeo, Hbs, HRCS, Hback⟩
            · iframe Hpkg HsrvM Hkvf' Hkvi' HW' Hr1 Hl1 HthT Hst Hbe Happ HKVc HRS
              iapply bkLendW_none
            -- (2026-11-06, `notes/begin-tok-plan.md`) the apply thread's token (`srvGoRes`'s) pays for
            -- the snapshot's reader slot; the reader goroutine's fork token comes back
            iunfold srvGoRes at Hgr
            icases Hgr with ⟨HgrW, HgT⟩
            iunfold taReplayField at HreplayField
            icases HreplayField with ⟨%terms, #Hterms⟩
            (try wp_auto)
            wp_apply (hCM s m sm sv.Metadata'.Term' sv.Metadata'.Index' (ciEff γ' st'.k) terms null cs' fv.lg kv' be dq RC RC'
                RS RS' Qd γr.raft (by rw [hci']; exact Int.le_refl _) hmo.2.1
              (by have h := Hsh.1.2.2.2.2.2.2.1 (Or.inr (Or.inr Hty)); exact ⟨h.1, h.2, Hsh.1.2.2.2.2.2.2.2⟩))
              $$ [Hlr Hkc HRC Hbeo Hbs HRCS Hm HgT]
              as %mg ⟨Hlr, HRS', Hbeo, HgT, %rc, %Dm, %cm, #Hmg, #Hml, #HszC, #Hcsom, %Hcml, Hrs, HQd⟩
            · iframe #; iframe Hlr Hkc HRC Hbeo Hbs HRCS Hm HgT
            ihave Hgr : srvGoRes s $$ [HgrW HgT]
            · iunfold srvGoRes; iframe HgrW HgT
            imod Hback $$ %Dm HRS' HQd Hbeo
              with ⟨%st3, HthT, Hst, Hbe, Happ, HKVc, HRS, #Hmimg, -, %Hst3⟩
            simp only [hci']
            ihave HRS : srvRest E' γr A' $$ [HRS]
            · rw [← srvRestM_false, ← HE'off]; iexact HRS
            ihave HKV := HKVk $$ HKVc
            iunfold apply.applyTok at HthT
            irename HthT => Hrdk
            -- the merged message sent: of a term committed through the applied index (the batch's
            -- term, `rnRtOk`; not `0`, a `MsgSnap`'s term), certified at the voters' conf state
            iunfold rnRtOk at Hrt
            rw [hγn]
            icases Hrt with (%Hrt0 | ⟨%ct, #Hct, %Hnct, %HbootCt, #Hbatch⟩)
            · exfalso
              exact (Hsh.1.2.2.2.1 (by rw [Hty]; simp [MsgSnap, MsgProp, MsgReadIndex,
                MsgTransferLeader])) Hrt0
            ihave #Hcv2 := Hcv
            iunfold epCsVoters at Hcv2
            icases Hcv2 with ⟨%c0, #Hc0, %Hcs0⟩
            ihave %Hcc := csOpt_agree cs' cm c0 $$ [Hcsom Hc0]
            · iframe Hcsom Hc0
            subst Hcc

            imod srv_merged_sent γr A' sv.Metadata'.Index' sv.Metadata'.Term' cm γn.id ct sm sn hpos
                hi61 (by have := hmo.2.1; omega) hlenZ hltA Hcs0 Hty hsn (by word)
                (by have := hnI; have := uint_nat_eq sv.Metadata'.Index'; omega)
              $$ [Hrli HA' Hsm Hct] with #Hsm'
            · iframe Hrli HA' Hsm Hct
            -- (S2's `merged_image`) the image's certificate
            imod merged_image s γ' ci TM' E' ρ γr sv.Metadata'.Index' A' x' Dm hoff' hlenZ ⟨hc0, hlog0⟩
              $$ [Hka] with ⟨Hka, #Himg'⟩
            · iframe Hsrv1 Hka Hmimg
            imod srvMerged_bundle γr.raft.raft m rc sm γn.id cm sv.Metadata'.Index'
                sv.Metadata'.Term' Dm Hty
              $$ [Hml HszC Hsm' Hrs Himg'] with Hbun
            · iframe Hml HszC Hsm' Hrs Himg'
            (try wp_auto)
            wp_apply (hSMS s mg m rc fv.lg fv.memberID stg tr γNt SN TSN lidt) $$ [Hgr Hlr Hbun]
              as ⟨Hgr, Hlr⟩
            · iframe #; iframe Hgr Hlr; rw [HγNt]; iframe Hbun
            (try wp_auto)
            have hF3 : loopOk γ' st3 sv.Metadata'.Index' ∧ ciEff γ' st3.k = sv.Metadata'.Index' :=
              ⟨Hst3.2.1, by rw [Hst3.2.2]; exact hci'⟩
            iapply Hfin $$ %st3 %hF3 Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS Hcursor HbootField Hao
          · (try wp_auto)
            wp_apply (hGTo.1 m (DFrac.own 1) DFrac.discard false sm) $$ [Hm] as Hm
            · iframe #; iframe Hm
            (try wp_auto)
            wp_apply (hRSn γm s sm.msg.To' (W64 2)) $$ []
            · iframe #
            (try wp_auto)
            iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS Hcursor HbootField Hao
        · itrivial
      iapply BigAndL.bigAndL_nil.2
      itrivial
    · -- `default`
      (try wp_auto)
      iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS Hcursor HbootField Hao
  | on γa =>
  have hon : E.authOn = true := by simp [apply.AEnv.authOn, hM, auth.AuthMode.isOn]
  rw [hon] at hch ⊢
  simp only [srvApplyKVM_true, kvAppliedM_true]
  wp_start as ⟨#Hsrv, #Hsa, #Hnid, #Hes, #Hesl, #Hsnf, Hsnv, ⟨#Hcert, #Hsloc⟩, #Hncf, #Hnc2, Hnr0,
    #Hracf, #Hracc, #Hrtf, #HreplayField, #Hrt, #Hmerge, Hcursor, HbootField, Hai, Hat, Hcs, Hss, Hst, Hbe, Happ, Hlr, Hgr, Hrdk, Hbr, HKV, Hao, #Hlog,
    #HW, HWA, Hka, HRS, HAR, #Hkv, HwalT, Hso, #HmetaSnap⟩
  icases srvApRes_cfg_size s γr _ $$ HAR with ⟨HAR, %hsz20⟩
  ihave #Hsrv' := Hsrv
  iunfold isServerM at Hsrv'
  icases Hsrv' with ⟨%Hρrd, -, ⟨%fv, #Hfl⟩, #Hatm, -, #HrnS, -⟩
  iunfold srvFieldsAtM at Hfl
  icases Hfl with ⟨#Hlgf, #Hlgnn, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, -⟩
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, ⟨%g, #Hg, #Hgs⟩, ⟨%bsl, #Hbsl⟩, -⟩
  ihave #Pbe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hatm' := Hatm
  iunfold srvAtomicsM at Hatm'
  icases Hatm' with ⟨#Hainv, -, #HkiM⟩
  ihave #Hkvi := srvKVInvsM_true s E γr $$ HkiM
  ihave #Hkvi2 := Hkvi
  iunfold srvKVInvsOn at Hkvi2
  icases Hkvi2 with ⟨#HkI0, -, #Hrli, -, -, %Hkvp, -, %Hcmlg, -⟩
  obtain ⟨⟨hw1, hw2, hw3, hw4⟩, -⟩ := Hkvp
  have Hcmf := Hcmlg.1
  -- the cluster runs auth on, the member's KV invariant says
  imod (kvInvOn_authOn γr.raft γr.kv srvAuthSt0) $$ HkI0 with %hao
  -- the applied auth state is the applied log's
  icases kvAppliedOn_sa γr A x sa $$ Hka with ⟨Hka, %hsa⟩
  subst hsa
  -- the snapshot path's resources: the bundle, the counter, the backend's own
  iunfold srvSnapOwn at Hso
  icases Hso with ⟨%γt, %nt, #Hro, %Hnt, Hγt, Hsres⟩
  ihave #Hro' := Hro
  iunfold srvSnapRO at Hro'
  icases Hro' with ⟨%cfg, %ss, %hk, %lgh, %stp, %γd, %idm, %al, %ast, %lp, %cl, %ps, %dir, %d,
    %Hp, #Hcflg, #Hcfzl, #Hcfdd, #Hcffg, #Hfg, #Hvoff, #Hcfq, #Hcfw, #Hssf, #Hssi, #Hhkf, #Hhk, #Hstp, #Hidm,
    #Hdinv, #Half, #Hauf, #Hlpf, #Hclf, #Hal, #HalOk, #HauOk, #HauR, #HauSK, #HlpOk, #HlpCfg, #Hrc,
    #HclOk, #Hvc, #Hmd, #Hks, #HlpI, #HlpM, ⟨#Hkvaddr, #Hkvm⟩, #Hcfg, #Hclgz, #Hsws⟩
  obtain ⟨hkb, hdbo, hmm, hbuq, hsl, hdirps, hsop, hbr, hci, hhk, hwf, hlim, hlp,
    halbi, hmbP, hRO, hrb, hdd⟩ := Hp
  -- (auth-lease S3a §5) the lessor's mode the KV names' (`Hmo`), any lease mode
  icases HlpM with ⟨%Hmo, #HlpM⟩
  icombine Hnid Hidm gives %Hidn
  subst Hidn
  -- the snapshot saved in the member's directory
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
  -- the snapshot's file out of the directory, the counter raised to its index and sealed with it (`snapDir_take`, `snapRmM_take`), its
  -- image certified in the mode `on` (`srvImageOn`)
  have hnt' : nt ≤ uint.nat sv.Metadata'.Index' := by
    have : uint.nat ag < uint.nat sv.Metadata'.Index' := by word  -- (route (C)) the ghost index
    omega
  wp_auto_lc 1
  ihave #Hdinv' : inv snapDirN (snapDirInv (config.snapDirOf cfg.DataDir') γd (srvImageOn γr.raft.raft) (snapRmM γt)) $$ []
  · rw [← srvImageM_on, ← hao]; iexact Hdinv
  ihave Htake := snapRmM_take (GF := GF) γt sv.Metadata'.Index' nt hnt'
  icases Htake with ⟨Hno, Hup⟩
  imod snapDir_take (config.snapDirOf cfg.DataDir') γd (srvImageOn γr.raft.raft) (snapRmM γt) sv.Metadata'.Index'
      (monoNatAuthOwn γt 1 nt) (monoNatAuthOwn γt 1 (uint.nat sv.Metadata'.Index' + 1))
      $$ Hlc1 Hdinv' Hsaved Hγt Hno Hup with ⟨%D, Hfile, #Himg⟩
  -- the image's facts (`snapRecv_imageOn`): its committed log `A'` extending `A`
  have hai0 : uint.Z ag = uint.Z γr.raft.ai0 + A.length := by
    rw [hraft]; have := hAL; word
  imod snapRecv_imageOnR γr.raft.raft γr E sv.Metadata'.Index' ag D d A x cl _ _ hkb hraft hc0 hch
      hlog0 hai0 hgi hboot hRO r0 hids $$ Hkvi Himg Hka HRS Hrc
    with ⟨Hka, HRS, %A', %u, #HA', %Hif, #Him0, #HCp0⟩
  -- the applied log's model and compaction revision (`-1`, a mode-on log compacts nothing; the
  -- apply thread's too, `srvApplyKVOn_crev`)
  iunfold kvAppliedOn at Hka
  icases Hka with ⟨HkaL0, %Hch0⟩
  iunfold kvAppliedLOn at HkaL0
  icases HkaL0 with ⟨#HA0, Hhi0, #Hc0, %He0⟩
  ihave Hka : kvAppliedOn γr.raft γr.kv srvAuthSt0 A x (srvAuthAtLog γr.kv srvAuthSt0 A)
      (kvLeasesOn γr.kv srvAuthSt0 A) $$ [Hhi0]
  · iunfold kvAppliedOn; iunfold kvAppliedLOn; iframe HA0 Hhi0 Hc0
    ipureintro; exact ⟨He0, Hch0⟩
  imod kv_log_plainOn γr.raft γr.kv srvAuthSt0 A $$ HkI0 Hrli HA0 with %HplA
  imod srvApplyKVOn_crev s E γr srvAuthSt0 ρ.wait x _ $$ Hkvi HKV with ⟨HKV, %Hxc⟩
  have HxA : x.log = kvModelOn γr.kv srvAuthSt0 A ∧ x.crev = crevOf γr.kv A := by
    refine ⟨?_, by rw [Hxc, crevOf_plainOn γr.kv A HplA]⟩
    unfold kvModelOn; rw [← He0]
  -- the KV's ghost state jumps to the image's log
  imod snapRecv_kv_jumpOn E γr A A' x _ Hif.pre (by have := Hif.hst.2; omega) $$ Hkvi Hka HA'
    with ⟨%Hxch, HkaL⟩
  obtain ⟨tI, hmeta⟩ := Hif.hmetaI
  -- the auth store's `Recover` facts at the image's log
  ihave #HauS : snapAuthResM E.authMode s ast E.RD γr A' $$ []
  · iapply snapAuthResM_on s ast E γr A' γa hM; iframe Hauf HauSK
  -- the backend's own resources
  iunfold srvSnapRes at Hsres
  icases Hsres with ⟨%d0, %al0, %dd, %Hkb0, Hstopc, Hbo, #Hal0, #Hdd, Hpath, -⟩
  obtain rfl := srvBkTie_inj d d0 (hkb.symm.trans Hkb0)
  icombine Half Hal0 gives %Hale
  subst Hale
  icombine Hcfdd Hdd gives %Hdde
  subst Hdde
  -- the apply thread's membership resources: the transport, the members' directory
  iunfold srvApRes at HAR
  icases HAR with ⟨%bh, %ix, %lgh', %tl, %lid, %cl', %lgc, %cid, %prs, #Hbhf, #Hbh, #Htrf, #Hmidf,
    #Hclf', #Hlgcf, #Hlgcnn, #Hcidf, Hmr, %Hpc, #Hdl⟩
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
  icases Hsa' with ⟨%wt, %msc, %sc, #Hwtf, #Hwt, #Hmscf, ⟨%γm, %Hγm, #Hmidm, -, #Hrnf, #Hrnsi⟩, #Hscf,
    ⟨%stg, #Hstgf, #Hstgc⟩, ⟨%scu, #Hscuf, -⟩, #Hinf, -,
    ⟨%tr, %γNt, %lidt, %SN, %TSN, #Htrf2, #Htr, %HγNt⟩, %Hkv0⟩
  ihave #Hcfg' := Hcfg $$ %sc %scu Hscf Hscuf
  -- `s.applySnapshot(ep, apply)`, in the mode `on`
  iunfold srvGoRes at Hgr
  icases Hgr with ⟨HgrW, HthT⟩
  have hposS : 0 < uint.Z sv.Metadata'.Index' := by have := hai; word
  imod snap_csIdCount γr.raft sv hposS hi61 hsz20 $$ Hrli Hcert with %hcsz
  have hS := hASnap s ep ap sn sv γ ci TM E ρ γr ai at0 sd0 nc
      { cfg with SnapshotCount' := sc, SnapshotCatchUpEntries' := scu } ss hk hai hcsz d D lgh hkb
      hdbo hsop ⟨hwf, hlim, hci, hhk⟩ hmm hdd tI hmeta st b (by omega) hpd
      al ast lp cl x A r0 hRO A' u (by rw [hon]; exact HxA) (by rw [hon]; exact Hif.hst)
      (by rw [hon]; exact Hif.nolease) hbr hlp γp hrb stp γd γt
      (srvImageOn γr.raft.raft) (uint.nat sv.Metadata'.Index' + 1) (Nat.le_refl _) Hif.halarm
      halbi hmbP Hif.hmemb _ Hif.himg γN tl c prs γN.dir ps' _ rfl Hdk.1 Hdk.2.1 Hcl sm0 cs
      cfg.ServerFeatureGate' cfg.QuotaBackendBytes' cfg.WarningApplyDuration' hbuq
      Hif.pre (by rw [hon]; exact Hif.hA') (by rw [hon]; exact Hif.hlease) (by rw [hraft]) Hmo hany
      (by rw [hM]; exact ⟨⟨halbi.2.1, halbi.2.2.1, halbi.2.2.2⟩, Hif.hauthI,
        by have := Hif.len; omega⟩)
      γnc γn q hns
  rw [hon] at hS
  simp only [srvApplyKVM_true, kvModelM_true] at hS
  wp_apply hS
    $$ [Hsnv Hnr0 Hai Hat Hsd0 Hlr Hbr Hfile Hpath Hst Hbe HKV HRS Htlive Hsm0 Hcs HbootField Hstopc
      Hbo HthT HwalT]
    as ⟨Hsapp, Hnr1, HthT, HbootField, HwalT⟩
  · iframe #; iframe
  (try wp_auto)
  ihave Hgr : srvGoRes s $$ [HgrW HthT]
  · iunfold srvGoRes; iframe HgrW HthT
  iunfold srvSnapAppliedM at Hsapp
  iunfold srvSnapAppliedOn at Hsapp
  iunfold srvSnapAppliedG at Hsapp
  icases Hsapp with ⟨%γ', %TM', %E', %b', %st', %d', %x', %cs', %L, %Hsa1, #Hsrv1, Hai, Hat, Hsd,
    Hsm, Hcs, #Hcso, Hst, Hbe, Hlr, Hbr, HKV, HRS, Hstopc, Hbo, Hγt, Hpath, #Hbf', Htlive,
    ⟨%kv', #Hkvf', #Hkvi', %Hkve⟩⟩
  obtain ⟨hbs, hkb', hP', hRO', hlo', hci', hxl, hxcr, hxch, hL⟩ := Hsa1
  -- the apply thread's reader token, at the new environment's store (`beSucc` keeps it)
  ihave Hrdk : mvcc.api.mvccReaders (GF := GF) E'.γ 1 $$ [Hrdk]
  · iapply (show mvcc.api.mvccReaders (GF := GF) E.γ 1 ⊢ mvcc.api.mvccReaders E'.γ 1 by
      obtain ⟨-, _, _, _, _, _, _, hE⟩ := hbs; rw [hE]; exact .rfl)
    iexact Hrdk
  have hM' : E'.authMode = auth.AuthMode.on γa := by
    obtain ⟨-, _, _, _, _, _, _, hE⟩ := hbs; rw [hE]; exact hM
  ihave HKV : srvApplyKVOn s E' ρ.wait x' (srvAuthAtLog γr.kv srvAuthSt0 A') $$ [HKV]
  · rw [← srvApplyKVM_true]; iexact HKV
  -- `s.applyEntries(ep, apply)`: no entries
  wp_apply hAE s ep ap es $$ []
  · iframe #
  (try wp_auto)
  -- `backend.VerifyBackendConsistency(s.Backend(), s.Logger(), true, schema.AllBuckets...)`
  wp_apply hBk s E.γbe $$ [Hbr] as %be ⟨Hbr, %dB, -, #HbRO⟩
  · iframe #; iframe Hbr
  -- (sweep repairs 1, B4) `ETCD_VERIFY` off, the backend's
  ihave #Hvoff := srvBeRO_etcdVerifyOff dB $$ HbRO
  wp_apply hLg s fv.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr
  (try wp_auto)
  wp_apply hV be fv.lg true bsl $$ []
  · iframe #
  (try wp_auto)
  -- `proposalsApplied.Set(float64(ep.appliedi))`
  iunfold gaugeSetSpec at Hgs
  wp_apply Hgs
  (try wp_auto)
  -- `s.applyWait.Trigger(ep.appliedi)`: the applied index jumps to the snapshot's, the auth state
  -- after the image's log published (`applied_jumpM`)
  ihave #Hsrv1' := Hsrv1
  iunfold isServerM at Hsrv1'
  icases Hsrv1' with ⟨-, -, -, #Hatm1, -, -⟩
  iunfold srvAtomicsM at Hatm1
  icases Hatm1 with ⟨#Hainv1, -, #HkiM1⟩
  ihave #Hkvi1 := srvKVInvsM_true s E' γr $$ HkiM1
  imod srvApplyKVOn_writer hPers hReach s E' γr srvAuthSt0 ρ.wait x' _ $$ Hkvi1 HKV
    with ⟨HKV, #Hic, -, -, -⟩
  have hiL : uint.Z sv.Metadata'.Index' = uint.Z γr.raft.ai0 + A'.length := by
    rw [hraft]; have := Hif.len; word
  have hxm : x'.log = kvModelOn γr.kv srvAuthSt0 A' := by rw [hxl]; rfl
  ihave #HkL : kvLogAtM true γr sv.Metadata'.Index' x'.log $$ []
  · iunfold kvLogAtM; iexists A'; iframe HA'; ipureintro; exact ⟨hiL, hxm⟩
  ihave Hka : kvAppliedOn γr.raft γr.kv srvAuthSt0 A' x' (srvAuthAtLog γr.kv srvAuthSt0 A')
      (kvLeasesOn γr.kv srvAuthSt0 A')
    $$ [HkaL]
  · iunfold kvAppliedOn
    isplitl
    · rw [hxm]; iexact HkaL
    ipureintro; rw [hxch, hon, hch]
  imod srvApplyKVOn_appliedPub s E' ρ.wait x' _ γa hM' γr A' sv.Metadata'.Index' hiL $$ HKV Hka
    with ⟨HKV, Hka, #Hpub⟩
  imod applied_jumpM true s E' γr ag sv.Metadata'.Index' x.log x'.log hgi
      (by rw [hxm, HxA.1]; exact kvModelOn_prefix γr.kv srvAuthSt0 Hif.pre)
    $$ Hainv1 Hao Hlog HkL Hic Hpub with ⟨Hao, #Hlb, #Hlog1⟩
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
  -- the post's facts: the voters, the log's last term, the membership resource at `A'`, the
  -- snapshot path's resources at the new backend
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
  imod kv_log_ccOkOn γr.raft γr.kv srvAuthSt0 A' $$ HkI0 Hrli HA' with %Hcc
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
    · iexact Hlgcnn
    isplitl [Htlive]
    · iunfold ccMembRes
      iframe Hrc'
      iexists γN, c, ps'
      iframe Htlive Hmd'
      ipureintro; exact ⟨Hcl, Hdk⟩
    ipureintro; exact ⟨hcov, hmo⟩
  ihave #Hro1 := srvSnapRO_succ s ci γr γt d d' al ast lp cl hbs hkb hkb' hP'
    hRO' $$ [Hro Half Hauf Hlpf Hclf]
  · iframe Hro Half Hauf Hlpf Hclf
  ihave Hso' : srvSnapOwn s ci E' γr γ' sv.Metadata'.Index' $$ [Hγt Hstopc Hbo Hpath]
  · iunfold srvSnapOwn
    iexists γt, uint.nat sv.Metadata'.Index' + 1
    iframe Hro1 Hγt
    isplitr
    · ipureintro; exact Nat.le_refl _
    iunfold srvSnapRes
    iexists d', al, cfg.DataDir'
    iframe Hstopc Hbo Half Hcfdd Hpath
    isplitr
    · ipureintro; exact hkb'
    iexact Hbf'
  iunfold epConfState at Hcs
  icases Hcs with ⟨Hcs, #Hcsok⟩
  -- the step's end, shared by the selects' branches: the apply thread at a state `stF` of the
  -- same consistent index
  ihave Hfin : iprop(∀ stF : ApplyState, ⌜loopOk γ' stF sv.Metadata'.Index' ∧
        ciEff γ' stF.k = sv.Metadata'.Index'⌝ -∗
      epAppliedIAddr ep ↦ sv.Metadata'.Index' -∗ epAppliedTAddr ep ↦ sv.Metadata'.Term' -∗
      epConfStateAddr ep ↦ cs' -∗ srvSnapState s ep mst γs sv.Metadata'.Index' (W64 0) -∗
      applyThread γ' stF -∗ applyBackend γ' ci b' -∗ ciApplying ci a t -∗ srvLgReader s -∗
      srvGoRes s -∗ mvcc.api.mvccReaders E'.γ 1 -∗
      srvApplyKVOn s E' ρ.wait x' (srvAuthAtLog γr.kv srvAuthSt0 A') -∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A' x' (srvAuthAtLog γr.kv srvAuthSt0 A')
      (kvLeasesOn γr.kv srvAuthSt0 A') -∗
      srvRestM true E' γr A' -∗ monoNatAuthOwn γr.cursor 1 n -∗ epReplayConfAddr ep ↦ (null : Loc) -∗ srvAppliedOwn γr sv.Metadata'.Index' -∗ Φ #()) $$ [HΦ Hbr HAR' HWA HwalT Hso']
  · iintro %stF %HF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS Hcursor HbootField Hao
    ihave Hcs : epConfState ep cs' $$ [Hcs]
    · iunfold epConfState; iframe Hcs Hcsok
    iapply HΦ
    iexists γ', TM', E', b', stF, A', cs'
    iframe Hcursor HbootField
    isplitr
    · ipureintro; exact hbs
    iframe Hsrv1 HAR' HA' Hai Hat Hcs Hecs Hss Hst Hbe Happ Hlr Hgr Hrdk Hbr Hao Hlb HWA HwalT Hso'
    isplitl [HKV Hka HRS]
    · iexists x'; iframe HKV Hlog1 Hka HRS
    isplitr
    · iexists kv'; iframe Hkvf' Hkvi'; ipureintro; exact Hkve
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
      iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS Hcursor HbootField Hao
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
  -- `select { case m := <-s.r.msgSnapC: ...; default: }`, as `wp_proofOn`'s at the snapshot's index
  have hF : loopOk γ' st' sv.Metadata'.Index' ∧ ciEff γ' st'.k = sv.Metadata'.Index' := ⟨hlo', hci'⟩
  have hlenZ : uint.Z sv.Metadata'.Index' = (A'.length : Int) := Hif.len
  iunfold srvMergeAttachment at Hmerge
  icases Hmerge with ⟨%srcChan, %pin, #Hcf, #Hmscb, #Hlocpin, #Htagpin⟩
  icombine Hmscf Hcf gives %hchan
  subst srcChan
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
        icases HP with ⟨%sm, Hm, %Hty, #Hsm, -, #Huf, #Hsrc⟩
        ihave %Hsh := (letI := srvStor (GF := GF) γn.node; sentMsg_shape γn.node.cl srvClusterN γn.id sm) $$ Hsm
        obtain ⟨sn, hsn, -⟩ := Hsh.2 Hty
        ihave Hidx := srv_merge_index γn γr pin ⟨m, sm⟩ sn rt n Hty hsn hbase
          $$ Hsrc Hrt Hsm Hlocpin Htagpin
        rw [hγn]
        letI := srvStor (GF := GF) γr.raft.raft
        ihave %Hsnp := srv_sentSnap_pos γr γn.id sm sn Hty hsn $$ [Hrli Hsm]
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
        iintro Hr1 Hl1
        iapply wp_value'
        repeat (
          fail_if_success wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
          first | wp_pure | wp_load | wp_store | wp_alloc_auto)
        wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
        iapply wp_go_step_receipt'
        case hv => first | rfl | simp [val.isPanic]
        inext
        iintro Hr2 Hl2
        iapply wp_value'
        (try wp_auto)
        wp_apply (hGT.1 m (DFrac.own 1) DFrac.discard false sm) $$ [Hm] as Hm
        · iframe #; iframe Hm
        (try wp_auto)
        wp_if_destruct
        · -- The message belongs to the term of this apply batch.
          ihave ⟨Hcursor, %hidxRaft⟩ := Hidx $$ %True.intro Hcursor
          (try wp_auto)
          -- Installing this snapshot already established the backend index at the apply cursor.
          ihave #HW' : srvWTPool E' γp $$ []
          · obtain ⟨-, p, P, f, cc, RO, RW, hE⟩ := hbs
            rw [hE]
            iunfold srvWTPool at HW
            unfold srvWTPool
            rw [show (E.onBe p P f cc RO RW).γbe = E.γbe from rfl]
            iexact HW
          icases srvApplyKVOn_coreA s E' ρ.wait x' _ $$ HKV with ⟨%ua, HKVc, HAr, HKVk⟩
          -- (#7-on) the auth row lends the auth buckets to the window
          ihave HL := srvAuthApplyResB_lend s E' (srvAuthAtLog γr.kv srvAuthSt0 A') γa hM' (srvAuthAtLog_rev_pos γr.kv A') $$ HAr
          -- the apply goroutine's tokens (`apply.applyTok`), lent to the commit
          ihave HthT : apply.applyTok (GF := GF) E' $$ [Hrdk]
          · iunfold apply.applyTok; iexact Hrdk
          -- (auth-lease S3a §5) the window at the mode's table
          have HE'on : E'.authOn = true := by unfold apply.AEnv.authOn; rw [hM']; rfl
          ihave HRS : srvRestM E'.authOn E' γr A' $$ [HRS]
          · rw [HE'on]; iexact HRS
          imod mergedCreate_window hsh hPers hReach hImg hSnap hOn hSave hPut hUR hID hName hSafe true
              s γ' ci TM' E' ρ γr b' st' sv.Metadata'.Index' a t A' x' ρ.wait γp ua kv' hlo'
              auth.authBkts (authBucketsAt (srvAuthAtLog γr.kv srvAuthSt0 A'))
              (srvAuthApplyResB s E' (srvAuthAtLog γr.kv srvAuthSt0 A')) authBkts_rest
            $$ [Hst Hbe Happ HKVc HRS Hr1 Hl1 HthT HL]
            with ⟨%be, %dq, %RC, %RC', %RS, %RS', %Qd, Hkc, HRC, Hbeo, Hbs, HRCS, Hback⟩
          · iframe Hpkg Hsrv1 Hkvf' Hkvi' HW' Hr1 Hl1 HthT Hst Hbe Happ HKVc HRS HL
          -- (2026-11-06, `notes/begin-tok-plan.md`) the apply thread's token (`srvGoRes`'s) pays for
          -- the snapshot's reader slot; the reader goroutine's fork token comes back
          iunfold srvGoRes at Hgr
          icases Hgr with ⟨HgrW, HgT⟩
          iunfold taReplayField at HreplayField
          icases HreplayField with ⟨%terms, #Hterms⟩
          (try wp_auto)
          wp_apply (hCM s m sm sv.Metadata'.Term' sv.Metadata'.Index' (ciEff γ' st'.k) terms null cs' fv.lg kv' be dq RC RC'
              RS RS' Qd γr.raft (by rw [hci']; exact Int.le_refl _) hmo.2.1
              (by have h := Hsh.1.2.2.2.2.2.2.1 (Or.inr (Or.inr Hty)); exact ⟨h.1, h.2, Hsh.1.2.2.2.2.2.2.2⟩))
            $$ [Hlr Hkc HRC Hbeo Hbs HRCS Hm HgT]
            as %mg ⟨Hlr, HRS', Hbeo, HgT, %rc, %Dm, %cm, #Hmg, #Hml, #HszC, #Hcsom, %Hcml, Hrs, HQd⟩
          · iframe #; iframe Hlr Hkc HRC Hbeo Hbs HRCS Hm HgT
          ihave Hgr : srvGoRes s $$ [HgrW HgT]
          · iunfold srvGoRes; iframe HgrW HgT
          imod Hback $$ %Dm HRS' HQd Hbeo
            with ⟨%st3, HthT, Hst, Hbe, Happ, HKVc, HRS, #Hmimg, HAr, %Hst3⟩
          simp only [hci']
          ihave HRS : srvRestM true E' γr A' $$ [HRS]
          · rw [← HE'on]; iexact HRS
          ihave HKV := HKVk $$ HKVc HAr
          iunfold apply.applyTok at HthT
          irename HthT => Hrdk
          -- the apply thread's compaction revision `-1` (the image's log's, a mode-on one)
          imod kv_log_plainOn γr.raft γr.kv srvAuthSt0 A' $$ HkI0 Hrli HA' with %HplA'
          have hcr : x'.crev = -1 := by rw [hxcr]; exact crevOf_plainOn γr.kv A' HplA'
          -- the merged message sent: of a term committed through the applied index (the batch's
          -- term, `rnRtOk`; not `0`, a `MsgSnap`'s term), certified at the voters' conf state
          iunfold rnRtOk at Hrt
          rw [hγn]
          icases Hrt with (%Hrt0 | ⟨%ct, #Hct, %Hnct, %HbootCt, #Hbatch⟩)
          · exfalso
            exact (Hsh.1.2.2.2.1 (by rw [Hty]; simp [MsgSnap, MsgProp, MsgReadIndex,
              MsgTransferLeader])) Hrt0
          ihave #Hcv2 := Hcv
          iunfold epCsVoters at Hcv2
          icases Hcv2 with ⟨%c0, #Hc0, %Hcs0⟩
          ihave %Hcc := csOpt_agree cs' cm c0 $$ [Hcsom Hc0]
          · iframe Hcsom Hc0
          subst Hcc

          imod srv_merged_sent γr A' sv.Metadata'.Index' sv.Metadata'.Term' cm γn.id ct sm sn hpos
              hi61 (by have := hmo.2.1; omega) hlenZ hltA Hcs0 Hty hsn (by word)
              (by have := hnI; have := uint_nat_eq sv.Metadata'.Index'; omega)
            $$ [Hrli HA' Hsm Hct] with #Hsm'
          · iframe Hrli HA' Hsm Hct
          -- (#7-on's `merged_imageOn`) the image's certificate: the auth buckets the lent part's
          ihave Hmi : |={⊤}=> kvAppliedOn γr.raft γr.kv srvAuthSt0 A' x'
                (srvAuthAtLog γr.kv srvAuthSt0 A') (kvLeasesOn γr.kv srvAuthSt0 A') ∗
              □ (srvNet (GF := GF) γr.raft.raft).img sv.Metadata'.Index' Dm $$ [Hka]
          · iapply (merged_imageOn s γ' ci TM' E' ρ γr γa sv.Metadata'.Index' A' x' _ Dm hM'
              hlenZ ⟨hc0, hlog0⟩ hcr)
            iframe Hsrv1 Hka Hmimg; ipureintro
            obtain ⟨r0, hQ, hr⟩ := Hst3.1
            exact authBucketsAt_congr _ Dm r0 hr hQ
          imod Hmi with ⟨Hka, #Himg'⟩
          imod srvMerged_bundle γr.raft.raft m rc sm γn.id cm sv.Metadata'.Index'
              sv.Metadata'.Term' Dm Hty
            $$ [Hml HszC Hsm' Hrs Himg'] with Hbun
          · iframe Hml HszC Hsm' Hrs Himg'
          (try wp_auto)
          wp_apply (hSMS s mg m rc fv.lg fv.memberID stg tr γNt SN TSN lidt) $$ [Hgr Hlr Hbun]
            as ⟨Hgr, Hlr⟩
          · iframe #; iframe Hgr Hlr; rw [HγNt]; iframe Hbun
          (try wp_auto)
          have hF3 : loopOk γ' st3 sv.Metadata'.Index' ∧ ciEff γ' st3.k = sv.Metadata'.Index' :=
            ⟨Hst3.2.1, by rw [Hst3.2.2]; exact hci'⟩
          iapply Hfin $$ %st3 %hF3 Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS Hcursor HbootField Hao
        · (try wp_auto)
          wp_apply (hGTo.1 m (DFrac.own 1) DFrac.discard false sm) $$ [Hm] as Hm
          · iframe #; iframe Hm
          (try wp_auto)
          wp_apply (hRSn γm s sm.msg.To' (W64 2)) $$ []
          · iframe #
          (try wp_auto)
          iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS Hcursor HbootField Hao
      · itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- `default`
    (try wp_auto)
    iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS Hcursor HbootField Hao
end proof

end EtcdGrove
end Perennial
