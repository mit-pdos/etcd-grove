/-
**`applyAll` on a snapshot payload, in the server's auth mode** (the auth-on snapshot plan's P6.3,
2026-11-03): `EtcdServer.applyAll.specSnapM` over `applySnapshot.specSnapM`, its `off` case lean's
`applyAll.specSnap` (`ApplyAllSnap.lean`), its `on` case `wp_proofSnap`'s twin: the image's facts
in the mode (`snapRecv_imageOn`), the KV's ghost state's jump (`snapRecv_kv_jumpOn`), the applied
index's with the auth state published (`srvApplyKVOn_appliedPub`, `applied_jumpM`), and the merge
branch as `applyAll.wp_proofBatch`'s on (`merged_imageOn`, through `merged_imageC`). Lean-first. `run`'s auth-on snapshot case uses
it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyAllSnap
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.MergedImageOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapAuthRecover

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

/-- **The applied auth state is the applied log's** (`kvAppliedOn`'s model). -/
theorem kvAppliedOn_sa (γr : ReadNames) (A : List EntryModel) (x : apply.ApplyKV)
    (sa : auth.AuthState) :
    kvAppliedOn (GF := GF) γr.raft γr.kv srvAuthSt0 A x sa ⊢
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗ ⌜sa = srvAuthAtLog γr.kv srvAuthSt0 A⌝ := by
  iintro H
  iunfold kvAppliedOn at H
  icases H with ⟨Hl, %Hch⟩
  iunfold kvAppliedLOn at Hl
  icases Hl with ⟨H1, H2, H3, %He⟩
  isplitl
  · iunfold kvAppliedOn; iunfold kvAppliedLOn; iframe H1 H2 H3; ipureintro; exact ⟨He, Hch⟩
  ipureintro
  unfold srvAuthAtLog
  rw [← He]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem EtcdServer.applyAll.wp_proofSnapM
    (hSnapOff : EtcdServer.applyAll.specSnap (GF := GF) (hG := hG))
    (hASnap : EtcdServer.applySnapshot.specSnapM (GF := GF) (hG := hG))
    (hAE : EtcdServer.applyEntries.specNil (GF := GF) (hG := hG))
    (hBk : EtcdServer.Backend.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hV : backend.VerifyBackendConsistency.spec (GF := GF) (hG := hG))
    (hSINC : EtcdServer.snapshotIfNeededAndCompactRaftLog.specNoop (GF := GF) (hG := hG))
    -- the merge branch, as `wp_proofOn`'s
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
    EtcdServer.applyAll.specSnapM (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr b ep ap es sn sv rac nc st ai at0 a t cs x A mst γs γp γnc w nid nk q γn rt n
    sa hany hai hi61 hboot hAL hcia hraft hc0 hch hlog0 hγn hnI
  cases hM : E.authMode with
  | any => exact absurd hM hany
  | off =>
    have hon : E.authOn = false := by simp [apply.AEnv.authOn, hM]
    rw [hon] at hch ⊢
    exact hSnapOff s γ ci TM E ρ γr b ep ap es sn sv rac nc st ai at0 a t cs x A mst γs γp γnc w nid
      nk q γn rt n hai hi61 hboot hAL hcia hraft hc0 hch hlog0 hγn (by rw [hraft]) hnI
  | on γa =>
  have hon : E.authOn = true := by simp [apply.AEnv.authOn, hM, auth.AuthMode.isOn]
  rw [hon] at hch ⊢
  simp only [srvApplyKVM_true, kvAppliedM_true]
  wp_start as ⟨#Hsrv, #Hsa, #Hnid, #Hes, #Hesl, #Hsnf, Hsnv, ⟨#Hcert, #Hsloc⟩, #Hncf, #Hnc2, Hnr0,
    #Hracf, #Hracc, #Hrtf, #Hrt, Hai, Hat, Hcs, Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, HKV, Hao, #Hlog,
    #HW, HWA, Hka, HRS, HAR, #Hkv, HwalT, Hso, #HmetaSnap⟩
  ihave #Hsrv' := Hsrv
  iunfold isServerM at Hsrv'
  icases Hsrv' with ⟨%Hρrd, -, ⟨%fv, #Hfl⟩, #Hatm, -, #HrnS, -⟩
  iunfold srvFieldsAtM at Hfl
  icases Hfl with ⟨#Hlgf, %Hlgnn, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, -⟩
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
  icases Hkvi2 with ⟨#HkI0, -, #Hrli, -, -, -, %Hcmlg⟩
  have Hcmf := Hcmlg.1
  -- (the lease-expiry plan's S2–S4, 2026-11-05: until then the spec's premise) auth on, the
  -- cluster grants none (`srvKVInvsOn`'s)
  have hlgk : γr.kv.lg = false := Hcmlg.2
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
    %Hp, #Hcflg, #Hcfdd, #Hcffg, #Hfg, #Hcfq, #Hcfw, #Hssf, #Hssi, #Hhkf, #Hhk, #Hstp, #Hidm,
    #Hdinv, #Half, #Hauf, #Hlpf, #Hclf, #Hal, #HalOk, #HauOk, #HauR, #HauSK, #HlpOk, #HlpCfg, #HlpL, #Hrc,
    #HclOk, #Hvc, #Hmd, #Hks, #HlpI, #HlpM, #Hws, #Hcfg⟩
  obtain ⟨hkb, hlg, hstp, hdbo, hmm, hbuq, hsl, hdirps, hsop, hcm, hbr, hci, hhk, hwf, hlim, hlp,
    halbi, hwq, hRO, hrb⟩ := Hp
  -- (the lease-grant stage, 2.9) the lessor revocable refutes the rest's leased arm
  -- (the lease-expiry plan's X2) the mode of a cluster that grants none: `none`
  icases HlpM with ⟨%Hmo, #HlpM⟩
  have hEm : E.lm = .none := by
    have h := hlgk; rw [KVNames.lg_eq, ← Hmo] at h; simpa using h
  ihave #HlpM : lease.lessorModeIs E.γ.leases (decide (lease.Mode.none = .mono)) $$ []
  · iExactEq HlpM <;> rw [hEm]
  ihave #Hlrev : lease.lessorModeIs E.γ.leases false $$ []
  · iExactEq HlpM <;> rfl
  ihave ⟨%HElg, HRS⟩ := srvRest_revocable E γr A .none (by decide)
    (by rw [apply.AEnv.lg_eq, hEm]) $$ [$HlpM $Hlrev $HRS]
  ihave #HlpE : lease.lessorModeIs E.γ.leases (decide (E.lm = .mono)) $$ []
  · rw [hEm]; iexact HlpM
  rw [← srvRest_false E γr A HElg]
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
  -- the snapshot's file out of the directory, the counter raised to its index (`snapDir_take`), its
  -- image certified in the mode `on` (`srvImageOn`)
  have hnt' : nt < uint.nat sv.Metadata'.Index' := by
    have : uint.nat ai < uint.nat sv.Metadata'.Index' := by word
    omega
  wp_auto_lc 1
  ihave #Hdinv' : inv snapDirN (snapDirInv ss γd (srvImageOn γr.raft.raft) (srvSnapRm γt γr)) $$ []
  · rw [← srvImageM_on, ← hao]; iexact Hdinv
  imod snapDir_take ss γd γt γr (srvImageOn γr.raft.raft) sv.Metadata'.Index' ai nt hnt' hai
    $$ Hlc1 Hdinv' Hsaved Hγt Hao with ⟨Hγt, Hao, %D, Hfile, #Himg⟩
  -- the image's facts (`snapRecv_imageOn`): its committed log `A'` extending `A`
  have hai0 : uint.Z ai = uint.Z γr.raft.ai0 + A.length := by
    rw [hraft]; have := hAL; word
  imod snapRecv_imageOn γr.raft.raft γr E sv.Metadata'.Index' ai D d A x cl _ _ hkb hraft hc0 hch
      hlog0 hai0 hai hboot hRO HElg $$ Hkvi Himg Hka HRS Hrc
    with ⟨Hka, HRS, %A', %R, %r, #HA', %Hif, #Hrc0, #Hpf0, #Hpc0⟩
  -- the KV's ghost state jumps to the image's log
  imod snapRecv_kv_jumpOn E γr A A' x _ Hif.pre Hif.hlen $$ Hkvi Hka HA' with ⟨%Hxch, #Hcert', HkaL⟩
  ihave #HcertK : mvcc.certOk E.γ ([[], []] ++ R) $$ []
  · rw [Hif.log]; iexact Hcert'
  obtain ⟨tI, hmeta⟩ := Hif.hmetaI
  -- the auth store's `Recover` facts at the image's log
  ihave #HauS : snapAuthResM E.authMode s ast E.RD γr A' $$ []
  · iapply snapAuthResM_on s ast E γr A' γa hM; iframe Hauf HauSK
  -- the backend's own resources
  iunfold srvSnapRes at Hsres
  icases Hsres with ⟨%d0, %al0, %dd, %Hkb0, Hstopc, Hbo, #Hal0, HKC, #Hdd, Hpath, -⟩
  rw [hkb] at Hkb0
  cases Hkb0
  icombine Half Hal0 gives %Hale
  subst Hale
  icombine Hcfdd Hdd gives %Hdde
  subst Hdde
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
  -- `s.applySnapshot(ep, apply)`, in the mode `on`
  iunfold srvGoRes at Hgr
  icases Hgr with ⟨HgrW, HthT⟩
  have hS := hASnap s ep ap sn sv γ ci TM E ρ γr ai at0 sd0 nc
      { cfg with SnapshotCount' := sc, SnapshotCatchUpEntries' := scu } ss hk hai d D lgh hkb
      hdbo hsop ⟨hwf, hlim, hci, hhk⟩ hlg hmm tI hmeta st b (by omega)
      al ast lp cl x A hRO hwq R Hif.hpre Hif.hRok r
      (fun h => by rw [hcm, Hcmf] at h; cases h) Hif.hkI hbr hlp γp hrb stp γd γt
      (srvImageOn γr.raft.raft) (uint.nat sv.Metadata'.Index') hstp (Nat.le_refl _) Hif.halarm
      halbi Hif.hmemb _ Hif.himg γN tl c prs γN.dir ps' _ rfl Hdk.1 Hdk.2.1 Hcl sm0 cs
      cfg.ServerFeatureGate' cfg.QuotaBackendBytes' cfg.WarningApplyDuration' hbuq A'
      Hif.pre (by rw [hon]; exact Hif.hA') Hif.hlease (by rw [hraft]) Hmo hany
      (by rw [hM]; exact ⟨⟨halbi.2.1, halbi.2.2.1, halbi.2.2.2⟩, Hif.hauthI,
        by have := Hif.len; omega⟩)
      γnc
  rw [hon] at hS
  simp only [srvApplyKVM_true] at hS
  wp_apply hS
    $$ [Hsnv Hnr0 Hai Hat Hsd0 Hlr Hbr Hfile Hpath Hst Hbe HKV HRS HKC Hγt Htlive Hsm0 Hcs Hstopc
      Hbo HthT]
    as ⟨Hsapp, Hnr1, HthT⟩
  · iframe #; iframe
  (try wp_auto)
  ihave Hgr : srvGoRes s $$ [HgrW HthT]
  · iunfold srvGoRes; iframe HgrW HthT
  iunfold srvSnapAppliedM at Hsapp
  iunfold srvSnapAppliedOn at Hsapp
  iunfold srvSnapAppliedG at Hsapp
  icases Hsapp with ⟨%γ', %TM', %E', %b', %st', %d', %x', %cs', %L, %Hsa1, #Hsrv1, Hai, Hat, Hsd,
    Hsm, Hcs, #Hcso, Hst, Hbe, Hlr, Hbr, HKV, HRS, HKC, Hstopc, Hbo, Hγt, Hpath, #Hbf', Htlive,
    ⟨%kv', #Hkvf', #Hkvi'⟩⟩
  obtain ⟨hbs, hkb', hcm', hP', hRO', hlo', hci', hxl, hxcr, hxch, hL⟩ := Hsa1
  have hM' : E'.authMode = auth.AuthMode.on γa := by
    obtain ⟨-, _, _, _, _, _, _, hE⟩ := hbs; rw [hE]; exact hM
  ihave HKV : srvApplyKVOn s E' ρ.wait x' (srvAuthAtLog γr.kv srvAuthSt0 A') $$ [HKV]
  · rw [← srvApplyKVM_true]; iexact HKV
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
  -- `s.applyWait.Trigger(ep.appliedi)`: the applied index jumps to the snapshot's, the auth state
  -- after the image's log published (`applied_jumpM`)
  ihave #Hsrv1' := Hsrv1
  iunfold isServerM at Hsrv1'
  icases Hsrv1' with ⟨-, -, -, #Hatm1, -, -⟩
  iunfold srvAtomicsM at Hatm1
  icases Hatm1 with ⟨#Hainv1, -, -⟩
  icases srvApplyKVOn_idxCert s E' ρ.wait x' _ $$ HKV with ⟨HKV, #Hic, -⟩
  have hiL : uint.Z sv.Metadata'.Index' = uint.Z γr.raft.ai0 + A'.length := by
    rw [hraft]; have := Hif.len; word
  have hxm : x'.log = kvModelOn γr.kv srvAuthSt0 A' := by rw [hxl]; exact Hif.log
  ihave #HkL : kvLogAtM true γr sv.Metadata'.Index' x'.log $$ []
  · iunfold kvLogAtM; iexists A'; iframe HA'; ipureintro; exact ⟨hiL, hxm⟩
  ihave Hka : kvAppliedOn γr.raft γr.kv srvAuthSt0 A' x' (srvAuthAtLog γr.kv srvAuthSt0 A')
    $$ [HkaL]
  · iunfold kvAppliedOn
    isplitl
    · rw [hxm]; iexact HkaL
    ipureintro; rw [hxch, hon, hch]
  imod srvApplyKVOn_appliedPub s E' ρ.wait x' _ γa hM' γr A' sv.Metadata'.Index' hiL $$ HKV Hka
    with ⟨HKV, Hka, #Hpub⟩
  imod applied_jumpM true s E' γr ai sv.Metadata'.Index' x.log x'.log hai
      (by rw [hxl]; exact Hif.hpre)
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
    · ipureintro; exact Hlgcnn
    isplitl [Htlive]
    · iunfold ccMembRes
      iframe Hrc'
      iexists γN, c, ps'
      iframe Htlive Hmd'
      ipureintro; exact ⟨Hcl, Hdk⟩
    ipureintro; exact ⟨hcov, hmo⟩
  ihave #Hro1 := srvSnapRO_succ s ci γr γt d d' al ast lp cl hbs hkb hkb' (hcm'.trans hcm) hP'
    hRO' $$ [Hro Half Hauf Hlpf Hclf]
  · iframe Hro Half Hauf Hlpf Hclf
  ihave Hso' : srvSnapOwn s ci E' γr γ' sv.Metadata'.Index' $$ [Hγt Hstopc Hbo HKC Hpath]
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
    iframe HKC
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
      srvGoRes s -∗ srvApplyKVOn s E' ρ.wait x' (srvAuthAtLog γr.kv srvAuthSt0 A') -∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A' x' (srvAuthAtLog γr.kv srvAuthSt0 A') -∗
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
  -- `select { case m := <-s.r.msgSnapC: ...; default: }`, as `wp_proofOn`'s at the snapshot's index
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
            ihave #HW' : srvWTPool E' γp $$ []
            · obtain ⟨-, p, P, f, cc, RO, RW, hE⟩ := hbs
              rw [hE]
              iunfold srvWTPool at HW
              unfold srvWTPool
              rw [show (E.onBe p P f cc RO RW).γbe = E.γbe from rfl]
              iexact HW
            icases srvApplyKVOn_coreA s E' ρ.wait x' _ $$ HKV with ⟨%ua, HKVc, HAr, HKVk⟩
            -- (#7-on) the auth row lends the auth buckets to the window
            ihave HL := srvAuthApplyResB_lend s E' _ γa hM' $$ HAr
            imod mergedCreate_window hC hSnap hOn hSave hPut hUR hID hName hSafe true s γ' ci TM' E'
                ρ γr b' st' sv.Metadata'.Index' a t A' x' ρ.wait γp ua kv' hlo' hci' hpos hlenZ
                auth.authBkts (authBucketsAt (srvAuthAtLog γr.kv srvAuthSt0 A'))
                (srvAuthApplyResB s E' (srvAuthAtLog γr.kv srvAuthSt0 A')) authBkts_rest
              $$ [Hst Hbe Happ HKVc HRS Hr1 Hl1 Hr2 Hl2 HL]
              with ⟨%be, %dq, %RC, %RC', %RS, %RS', Hkc, HRC, Hbeo, Hbs, HRCS, Hback⟩
            · iframe Hpkg Hsrv1 Hkvf' Hkvi' HW' Hlog1 HA' Hr1 Hl1 Hr2 Hl2 Hst Hbe Happ HKVc HRS HL
            wp_apply (hCM s m sm sv.Metadata'.Term' sv.Metadata'.Index' cs' fv.lg kv' be dq RC RC'
                RS RS' _)
              $$ [Hlr Hkc HRC Hbeo Hbs HRCS Hm]
              as %mg ⟨Hlr, HRS', Hbeo, %rc, %Dm, %cm, #Hmg, #Hml, #Hcsom, Hrs, %HQd⟩
            · iframe #; iframe Hlr Hkc HRC Hbeo Hbs HRCS Hm; ipureintro; exact Hlgnn
            imod Hback $$ HRS' Hbeo with ⟨%st3, Hst, Hbe, Happ, HKVc, HRS, HAr, %Hst3⟩
            ihave HKV := HKVk $$ HKVc HAr
            icases srvApplyKVOn_idxCert s E' ρ.wait x' _ $$ HKV with ⟨HKV, #Hicx, -⟩
            ihave #Hrcx := mvcc.idxCert_rcpt E'.γ.idx x'.log $$ Hicx
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
                hi61 hmo.2.1 hlenZ hltA Hcs0 Hty hsn (by word)
                (by have := hnI; have := uint_nat_eq sv.Metadata'.Index'; omega)
              $$ [Hrli HA' Hsm Hct] with #Hsm'
            · iframe Hrli HA' Hsm Hct
            -- (#7-on's `merged_imageOn`) the image's certificate: the auth buckets the lent part's
            ihave Hmi : |={⊤}=> kvAppliedOn γr.raft γr.kv srvAuthSt0 A' x'
                  (srvAuthAtLog γr.kv srvAuthSt0 A') ∗
                □ (srvNet (GF := GF) γr.raft.raft).img sv.Metadata'.Index' Dm $$ [Hka]
            · iapply (merged_imageOn s γ' ci TM' E' ρ γr γa sv.Metadata'.Index' A' x' _ Dm hM'
                hlenZ ⟨hc0, hlog0⟩)
              iframe Hsrv1 Hka Hrcx; ipureintro
              obtain ⟨h1, r0, hQ, hr⟩ := HQd
              exact ⟨h1, authBucketsAt_congr _ Dm r0 hr hQ⟩
            imod Hmi with ⟨Hka, #Himg'⟩
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
