/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applyAll.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyAll
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applySnapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntries
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Backend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__snapshotIfNeededAndCompactRaftLog
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ModeSpecs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SDRun
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SDSnapLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.VerifyBackendConsistency
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetSnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ReportSnapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__ConsistentIndex
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapSendBranch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyAllSnap
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.MergedImageOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRecvOn

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
/-- **`applyAll.specBatch`**, at a restart point (R2d'a swap batch 3, 2026-11-06: the restart form,
until then `ApplyAllR.lean`'s `wp_proofBatchR`; the first-start proof deleted): one proof over the
slot `C` (the auth component's stage 2c), its rows at the mode's (`AuthCompRows`' bridges), over
`applyEntries.specBatch`, the merged snapshot's window lent the component's buckets (`acRes_lend`;
none off) and its image certified by `merged_imageC`. The same-term branch opens the
frozen backend at its durable index, including during replay. -/
theorem EtcdServer.applyAll.wp_proofBatch
    (hASnap : EtcdServer.applySnapshot.spec (GF := GF) (hG := hG))
    (hAE : EtcdServer.applyEntries.spec (GF := GF) (hG := hG))
    (hBk : EtcdServer.Backend.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hV : backend.VerifyBackendConsistency.spec (GF := GF) (hG := hG))
    (hSINC : EtcdServer.snapshotIfNeededAndCompactRaftLog.spec (GF := GF) (hG := hG))
    -- (2026-10-31, S1) the merge branch: the message's getters, the merge, the send, and what
    -- the snapshot window takes (`mergedCreate_window`)
    (hGT : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (hCM : EtcdServer.createMergedSnapshotMessage.spec (GF := GF) (hG := hG))
    (hSMS : EtcdServer.sendMergedSnap.spec (GF := GF) (hG := hG))
    -- A stale-term request still reports its failure to Raft.
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
    EtcdServer.applyAll.specBatch (GF := GF) (hG := hG) := by
  have hCMpast := EtcdServer.createMergedSnapshotMessage.caughtUp_of_spec hCM
  have hAE := hAE.1
  intro s γ ci TM C E ρ γr b ep ap es ents ms f0 rac nc st ai at0 a t cs x sa A mst γs γp dv γnc w nk
    q γn rt n rp g
  simp only [srvRunH_applyAll_specBatch]
  wp_start as ⟨%hP, #HsrvC, #Hsa, #Hbw, #Hes, #Hrac, #Hracc, #Hsn, #Hnc, #Hncb, Hnrc, #Hesl, #Hentsat, Hai, Hat, Hcs, #Hcv,
    Hss, Hst, Hbe, Happ, Hlr, Hgr, Hmr, Hbr, HKV, Hao, #Hlog, #Hbc, #HW, #HWA, Hka, HRS, #Hkb, Hdv, #Hdvr, HAR, Hrun, #Hsd, #Hkv, #Hmsi, HwalT, #Hrtf, #HreplayF0, #Hrt, #Hmerge, Hcursor, HbootField, Hso, HtokR⟩
  iunfold epReplayCfg at HbootField
  icases HbootField with ⟨%boot, HbootField, #HbootCfg⟩
  obtain ⟨hM, hRB, Hms, Hai1, Hok, hEok, hEpk, hdv, hAL, hAT, Hdisk, hciA, hcia, hg0, hγn, hpre, hnA, hbase, hbootLog, hnsw⟩ := hP
  have hon : E.authOn = C.isOn := by rw [apply.AEnv.authOn_eq, hM, AuthC.mode_isOn]
  -- (the auth component's stage 2c) the slot's rows at the mode's
  ihave #Hsrv := (isServerM_C C s γ ci TM E ρ γr).2 $$ HsrvC
  ihave HKV := (srvApplyKVM_C C s E ρ.wait x sa).2 $$ HKV
  ihave HtokR : srvTokRights E (ciEff γ st.k) $$ [HtokR]
  · rw [srvTokRights_eq C E _ hM]; iexact HtokR
  icases srvApRes_cfg_size s γr (ghostOf rp A) $$ HAR with ⟨HAR, %hsz20⟩
  have hsz : GMap.size γr.raft.raft.cfg < 2 ^ 61 := by omega
  ihave #Hsrv' := Hsrv
  iunfold isServerM at Hsrv'
  icases Hsrv' with ⟨%Hρrd, #Hsci, ⟨%sv, #Hfl⟩, -, -, #HrnS, -⟩
  iunfold srvFieldsAtM at Hfl
  icases Hfl with ⟨#Hlgf, #Hlgnn, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, -⟩
  ihave #Hsa' := Hsa
  iunfold isServerApplyAll at Hsa'
  icases Hsa' with ⟨%wt, %msc, %sc, #Hwtf, #Hwt, #Hmscf, ⟨%γb, %Hγb, #Hmidm, -, #Hrnf, #Hrnsi⟩, #Hsc,
    ⟨%stg, #Hstgf, #Hstgc⟩, -, #Hinf, -, ⟨%tr, %γN, %lid, %SN, %TSN, #Htrf, #Htr, %HγN⟩, %Hkv0⟩
  ihave #HstgS := Hstgc
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, ⟨%gI, #Hg, #Hgs⟩, ⟨%bsl, #Hbsl⟩, -⟩
  ihave #Pbe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  -- (R2d'a) the batch's window facts (`kvBatchR`): Go's start index `ai₀ = 0`, the backend's log
  -- through the consistent index
  ihave #HkbR := Hkb
  iunfold kvBatchR at HkbR
  icases HkbR with ⟨-, -, %HkbP⟩
  obtain ⟨HkAi, -, HkA0, -, -, -⟩ := HkbP
  have hGl : ∀ G : List EntryModel, ((ghostOf rp G).length : Int) =
      G.length + (rp.A₀.length - G.length : Nat) := by
    intro G; rw [ghostOf_length]; push_cast; rfl
  wp_auto
  -- `s.applySnapshot(ep, apply)`: no snapshot
  wp_apply hASnap.1 s ep ap $$ []
  · iframe #
  (try wp_auto)
  -- `s.applyEntries(ep, apply)`, lending it `forceDiskSnapshot` (D14i)
  iunfold srvSnapState at Hss
  icases Hss with ⟨%sd0, %sm0, %sf0, Hsd0, Hsm0, Hsf0, %Hdm0, #Hmst, #Hslb0⟩
  ihave Hfs : srvFS s $$ [Hsf0]
  · iunfold srvFS; iexists _; iexact Hsf0
  have hAE1 := hAE s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr rp A γp dv w g sa
    (by rw [hM]; cases C <;> simp [AuthC.mode])
    hRB Hms Hai1 Hok
    (by rw [hon]; exact hEok) hEpk hdv hg0
  rw [hon] at hAE1
  simp only [srvRunH_applyEntries_spec] at hAE1
  wp_apply hAE1
    $$ [Hai Hat Hcs Hcv Hst Hbe Happ Hlr Hgr Hmr HKV Hao Hfs Hka HRS Hdv Hrun HAR HtokR]
    as ⟨Hfs, Hdv, Hrun, HAR, %st', %ai', %at', %a', %t', %cs', %g', Hai, Hat, Hcs, #Hcv', Hst, HtokR, Hbe, Happ, Hlr, Hgr, Hmr, Hao, #HWA',
      ⟨%x', %sa', HKV, %Hx', #Hlog', Hka, HRS⟩, %Hpost⟩
  · iframe #; iframe
  iunfold srvFS at Hfs
  icases Hfs with ⟨%sf1, Hsf1⟩
  obtain ⟨hg', hok', hai', hlen', hci', hat'⟩ := Hpost
  -- (R2d'a) the ghost index after the batch: at least Go's, at most the new consistent index
  have hgA := hGl A
  have hgB := hGl (A ++ unapplied ai ms)
  have hlAB : ((A ++ unapplied ai ms).length : Int) = A.length + (unapplied ai ms).length := by
    simp
  have hag : uint.Z ai' ≤ uint.Z g' := by omega
  have hciL0 : uint.Z ai' ≤ uint.Z (ciEff γ st'.k) := by
    rcases hci' with ⟨hun, hc⟩ | hc
    · rw [hun, List.length_nil] at hlen'; rw [hc]; omega
    · rw [hc]; omega
  have hciL : uint.Z g ≤ uint.Z (ciEff γ st.k) → uint.Z g' ≤ uint.Z (ciEff γ st'.k) := by
    intro h
    rcases hci' with ⟨hun, hc⟩ | hc
    · have hgg : g' = g := by
        have : A ++ unapplied ai ms = A := by rw [hun, List.append_nil]
        rw [this] at hg'; word
      rw [hc, hgg]; exact h
    · rw [hc]; omega
  -- (D22 J1b) the snapshot resources at the new ghost index (restart S6, CP2 route (C): `g ≤ g'`)
  have Hgg' : uint.Z g ≤ uint.Z g' := by
    have hm : (ghostOf rp A).length ≤ (ghostOf rp (A ++ unapplied ai ms)).length := by
      have h1 := hGl A; have h2 := hGl (A ++ unapplied ai ms); omega
    omega
  ihave Hso := srvSnapOwn_mono s ci E γr _ g g' Hgg' $$ Hso
  -- (restart S6a) the removal counter raised to the new applied index (`snapshot`'s `Release`),
  -- staying at most the ghost index plus one (`ai' ≤ g'`)
  iunfold srvSnapOwn at Hso
  icases Hso with ⟨%γm, %c, #Hsro, %Hc, Hγm, Hsres⟩
  imod snapRm_raise γm ai' g' c Hc (by word) $$ Hγm with ⟨%c', %Hc', Hγm, #Hrmlb⟩
  ihave #Hsdir := srvSnapDir_of_RO s ci E γr γm $$ Hsro
  ihave Hso : srvSnapOwn s ci E γr γ g' $$ [Hγm Hsres]
  · iunfold srvSnapOwn; iexists γm, c'; iframe Hsro Hγm Hsres; ipureintro; exact Hc'
  ihave Hss : srvSnapState s ep mst γs ai' (W64 0) $$ [Hsd0 Hsm0 Hsf1]
  · iunfold srvSnapState; iexists _, _, _; iframe Hsd0 Hsm0 Hsf1 Hmst Hslb0
    ipureintro; exact ⟨by have := Hdm0.1; omega, by have := Hdm0.2; omega⟩
  (try wp_auto)
  -- `backend.VerifyBackendConsistency(s.Backend(), s.Logger(), true, schema.AllBuckets...)`
  wp_apply hBk s E.γbe $$ [Hbr] as %be ⟨Hbr, %dB, -, #HbRO⟩
  · iframe #; iframe Hbr
  -- (sweep repairs 1, B4) `ETCD_VERIFY` off, the backend's
  ihave #Hvoff := srvBeRO_etcdVerifyOff dB $$ HbRO
  wp_apply hLg s sv.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr
  (try wp_auto)
  wp_apply hV be sv.lg true bsl $$ []
  · iframe #
  (try wp_auto)
  -- `proposalsApplied.Set(float64(ep.appliedi))`
  iunfold gaugeSetSpec at Hgs
  wp_apply Hgs
  (try wp_auto)
  -- `s.applyWait.Trigger(ep.appliedi)`: the waiters through `ai'`
  icases srvAppliedOwn_lb γr g' $$ Hao with ⟨Hao, #Hlbg⟩
  ihave #Hlb : appliedAtLeast γr ai' $$ []
  · iunfold appliedAtLeast; iunfold appliedAtLeast at Hlbg
    iapply (monoNatLbOwn_le (GF := GF) (uint.nat ai') (by word)) $$ Hlbg
  iunfold isWaitTime at Hwt
  icases Hwt with ⟨%wi, %Hwi, -, #HTrig⟩
  subst Hwi
  wp_apply HTrig $$ []
  · iintro !>; iexact Hlb
  (try wp_auto)
  -- `<-apply.notifyc`: (D43 M3) the view after the batch deposited; (T10s3b B3) the batch's replay
  -- job taken, raft's first send's deposit
  wp_apply wp_notifyD_receive γnc nc (taReplayBatch ap γn rt n) _ $$ [Hnrc Hdv] as #HreplayField
  · iframe Hncb Hnrc Hdv
  (try wp_auto)
  -- (D19i part 1) `select { case <-apply.raftAdvancedC: case <-s.stopping: return }`: raft has
  -- advanced past the batch, or the server stops (no snapshot)
  iunfold rnAdvChan at Hracc
  icases Hracc with ⟨%γac, #Hracc⟩
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
      ihave HtokR : acTok C (ciEff γ st'.k) $$ [HtokR]
      · rw [← srvTokRights_eq C E _ hM]; iexact HtokR
      ihave HKV := (srvApplyKVM_C C s E ρ.wait x' sa').1 $$ HKV
      iapply HΦ
      iexists γ, TM, E, b, st', ai', at', a', t', cs', g'
      ihave HbootOut : epReplayCfg ep γr.raft rp.A₀.length (A ++ unapplied ai ms).length $$ [HbootField]
      · iunfold epReplayCfg
        iexists boot; iframe HbootField
        icases HbootCfg with (%h | #H)
        · ileft; ipureintro; simp only [List.length_append]; omega
        · iright; iexact H
      iframe Hcursor HbootOut
      iframe HsrvC
      isplitr
      · ipureintro; exact beSucc_refl γ E
      iframe Hai Hat Hcs Hcv' Hss Hst HtokR Hbe Happ Hlr Hgr Hmr Hbr HAR Hrun
      isplitl [Hao]
      · iexact Hao
      isplitr
      · iexact Hlbg
      isplitr
      · iexact HWA'
      isplitl [HKV Hka HRS]
      · iexists x', sa'; iframe HKV Hlog' Hka HRS; ipureintro; exact Hx'
      isplitr
      · iexact Hkv
      isplitl [HwalT]
      · iexact HwalT
      isplitl [Hso]
      · iexact Hso
      ipureintro; exact ⟨hg', hok', hai', hci'.imp_left And.right, hciL, hat'⟩
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
  iintro ⟨#Hadv, -⟩
  (try wp_auto)
  -- (#11) what the snapshot takes: `raftAdvancedC`'s payload (the node's applied index and the
  -- storage's past `ai'`, the batch's entries frozen with their terms), the log invariant
  -- (`raftPropose`'s), the batch's committed log (`kvBatch`'s), `ep.confState` the voters'
  have hρr : ρ.raft = γr.raft := by rw [← Hρrd]
  have hidx : (max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat =
      uint.nat ai' := by rw [← hai']; word
  have hlenA : uint.nat ai' = (A ++ unapplied ai ms).length := by
    rw [List.length_append]; have := hlen'; have := hAL; word
  have hltA : lastTermIs (A ++ unapplied ai ms) at' := lastTermIs_append hAT hat'
  icases Hadv with ⟨#Hnal, #Hsdl, -, #Hfts, #Hwh⟩
  ihave #Hnal' : (letI := srvStor (GF := GF) γr.raft.raft; nodeAppliedLb γr.raft.raft.cl nk (uint.nat ai')) $$ []
  · rw [← hidx, ← hρr]; iexact Hnal
  ihave #Hwh' : rnWalHanded γn (uint.nat ai') $$ []
  · rw [← hidx]; iexact Hwh
  ihave #HrnS' := HrnS
  iunfold srvRaftNode at HrnS'
  icases HrnS' with ⟨%rn0, -, HrpS⟩
  iunfold raftPropose at HrpS
  icases HrpS with ⟨%rni0, -, #Hrli, -⟩
  ihave #Hkb' := Hkb
  iunfold kvBatchR at Hkb'
  icases Hkb' with ⟨#HlbB, #HlbDisk, -⟩
  ihave %hcmp := srvRLogLb_prefix γr.raft (A ++ unapplied ai ms) rp.A₀ $$ [HlbB HlbDisk]
  · iframe HlbB HlbDisk
  ihave %hsmallDisk : ⌜rp.A₀.length < 2 ^ 61⌝ $$ []
  · ihave #Hinv : srvRaftLogInv γr.raft $$ []
    · rw [← hρr]; iexact Hrli
    iunfold srvRaftLogInv at Hinv
    icases Hinv with ⟨-, #Hcl, -⟩
    iunfold srvClusterOk at Hcl
    icases Hcl with ⟨-, -, -, #Hfits, -⟩
    iunfold srvRLogLb at HlbDisk
    icases HlbDisk with ⟨#HlogDisk, -⟩
    ihave %h := (letI := srvStor (GF := GF) γr.raft.raft
      isCommittedLogLb_small γr.raft.raft.cl srvClusterN _) $$ [Hfits HlogDisk]
    · iframe Hfits HlogDisk
    ipureintro
    simpa [srvLE, hpre] using h
  have hphysical : n = uint.nat ai' := by have := uint_nat_eq ai'; omega
  ihave #HcursorLb := monoNatLbOwn_get (GF := GF) γr.cursor 1 n $$ Hcursor
  ihave Hstor : srvSnapStor mst γs γr nk ai' at' $$ []
  · iunfold srvSnapStor
    isplitr
    · iunfold srvAttachedMem at Hmsi
      icases Hmsi with ⟨%pin, -, -, #Hinv⟩
      iunfold srvCreateMem
      iexists pin, γn.snap0; iexact Hinv
    isplitr
    · rw [← hphysical]; iexact HcursorLb
    isplitr
    · rw [← hidx, ← hρr]; iexact Hsdl
    isplitr
    · rw [← hρr]; iexact Hrli
    iexists A ++ unapplied ai ms
    iframe HlbB
    ipureintro; exact ⟨by rw [← hlenA]; try word, hltA⟩
  ihave ⟨#Hfz, #Hft⟩ := srv_frozen_of_terms γs (A ++ unapplied ai ms) ai' at' hlenA hltA $$ Hfts
  ihave #Hecs : iprop(⌜uint.Z ai' = 0⌝ ∨ epCsCfg γr cs') $$ []
  · by_cases hL : A ++ unapplied ai ms = []
    · ileft; ipureintro
      have h0 := congrArg List.length hL
      simp only [List.length_nil] at h0
      rw [h0] at hlenA; word
    · iright; iunfold epCsCfg; rw [← hρr]
      iapply epCsAt_ne _ _ _ (by unfold ghostOf; exact List.append_ne_nil_of_left_ne_nil hL _) $$ Hcv'
  -- `s.snapshotIfNeededAndCompactRaftLog(ep)`
  have hS1 := hSINC.1 s E ρ.wait γ ci b γr ep st' ai' at' cs' a' t' x' mst γs nk γp
    (w + (unapplied ai ms).length) TM ρ sa' q γn γm
  rw [hon] at hS1
  -- the apply thread's tokens (`apply.applyTok`: its reader token of the store)
  ihave Htt : apply.applyTok (GF := GF) E $$ [Hmr]
  · iunfold apply.applyTok; iexact Hmr
  wp_apply hS1 hok'
      hciL0 Hdisk.2 hsz hγn hpre
      (fun hm => by
        have h1 := hnsw hm; have h2 := hAL; have h3 := hlenA; rw [List.length_append] at h3
        have h4 := uint_nat_eq ai; omega)
    $$ [Hss Hai Hat Hcs Hst Hbe Happ Hlr HKV HwalT Hstor Htt]
    as ⟨%st'', Hss, -, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, HwalT, Htt, %Hst''⟩
  · iframe #; iframe
  iunfold apply.applyTok at Htt
  irename Htt => Hmr
  (try wp_auto)
  ihave HKV := (srvApplyKVM_C C s E ρ.wait x' sa').1 $$ HKV
  iunfold epConfState at Hcs
  icases Hcs with ⟨Hcs, #Hcsok⟩
  -- (2026-10-31, S1) the step's end, shared by the select's branches: the apply thread at a state
  -- `stF` of the same consistent index
  ihave Hfin : iprop(∀ stF : ApplyState, ⌜loopOk γ stF ai' ∧ ciEff γ stF.k = ciEff γ st'.k⌝ -∗
      epAppliedIAddr ep ↦ ai' -∗ epAppliedTAddr ep ↦ at' -∗ epConfStateAddr ep ↦ cs' -∗
      applyThread γ stF -∗ applyBackend γ ci b -∗ ciApplying ci a' t' -∗ srvLgReader s -∗
      srvGoRes s -∗ mvcc.api.mvccReaders E.γ 1 -∗ srvApplyKVC C s E ρ.wait x' sa' -∗
      kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 (ghostOf rp (A ++ unapplied ai ms)) x' sa' -∗
      srvRestRM C.isOn E γr rp (A ++ unapplied ai ms) -∗ monoNatAuthOwn γr.cursor 1 n -∗ epReplayConfAddr ep ↦ boot -∗ srvAppliedOwn γr g' -∗ Φ #()) $$ [HΦ Hss Hbr HAR Hrun HwalT HtokR Hso]
  · iintro %stF %HF Hai Hat Hcs Hst Hbe Happ Hlr Hgr Hmr HKV Hka HRS Hcursor HbootField Hao
    ihave Hcs : epConfState ep cs' $$ [Hcs]
    · iunfold epConfState; iframe Hcs Hcsok
    ihave HtokR : acTok C (ciEff γ stF.k) $$ [HtokR]
    · rw [HF.2, ← srvTokRights_eq C E _ hM]; iexact HtokR
    iapply HΦ
    iexists γ, TM, E, b, stF, ai', at', a', t', cs', g'
    ihave HbootOut : epReplayCfg ep γr.raft rp.A₀.length (A ++ unapplied ai ms).length $$ [HbootField]
    · iunfold epReplayCfg
      iexists boot; iframe HbootField
      icases HbootCfg with (%h | #H)
      · ileft; ipureintro; simp only [List.length_append]; omega
      · iright; iexact H
    iframe Hcursor HbootOut
    iframe HsrvC
    isplitr
    · ipureintro; exact beSucc_refl γ E
    iframe Hai Hat Hcs Hcv' Hss Hst HtokR Hbe Happ Hlr Hgr Hmr Hbr HAR Hrun
    isplitl [Hao]
    · iexact Hao
    isplitr
    · iexact Hlbg
    isplitr
    · iexact HWA'
    isplitl [HKV Hka HRS]
    · iexists x', sa'; iframe HKV Hlog' Hka HRS; ipureintro; exact Hx'
    isplitr
    · iexact Hkv
    isplitl [HwalT]
    · iexact HwalT
    isplitl [Hso]
    · iexact Hso
    ipureintro
    exact ⟨hg', HF.1, hai', by rw [HF.2]; exact hci'.imp_left And.right, by rw [HF.2]; exact hciL,
      hat'⟩
  -- `select { case m := <-s.r.msgSnapC: ...; default: }` (2026-10-31, S1: a `MsgSnap` raft handed
  -- out, merged with the backend's image and sent when the guard holds)
  -- (restart3 A1) the merged send's receive through `isServerApplyAll`'s bag, of the raft node `γm`
  -- (until then `srvSnapBagN` at the run's names)
  iunfold srvMergeAttachment at Hmerge
  icases Hmerge with ⟨%srcChan, %pin, #Hcf, #Hmscb, #Hlocpin, #Htagpin⟩
  icombine Hmscf Hcf gives %hchan
  subst srcChan
  iunfold isRNMsgSnapC at Hmscb
  icases Hmscb with ⟨%γc, #Hmscb⟩
  ihave #Hmscch := is_bag_is_chan γc msc _ $$ Hmscb
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hrli' : srvRaftLogInv γr.raft $$ []
  · rw [← hρr]; iexact Hrli
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
        ihave Hidx := srv_merge_index γn γr pin ⟨m, sm⟩ sn rt n Hty hsn hbase $$ Hsrc Hrt Hsm Hlocpin Htagpin
        rw [hγn]
        letI := srvStor (GF := GF) γr.raft.raft
        ihave %Hsnp := srv_sentSnap_pos γr γn.id sm sn Hty hsn $$ [Hrli' Hsm]
        · iframe Hrli' Hsm
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
          have hsentLe : uint.Z sn.Metadata'.Index' ≤ uint.Z ai' := by
            have := uint_nat_eq sn.Metadata'.Index'
            have := uint_nat_eq ai'
            omega
          iunfold taReplayBatch at HreplayField
          icases HreplayField with ⟨%terms, #Hterms, #Hjob⟩
          (try wp_auto)
          by_cases hnl : uint.Z (ciEff γ st''.k) ≤ uint.Z ai'
          · have hW : rp.A₀.length ≤ (A ++ unapplied ai ms).length := by
              have hge : uint.Z (ciEff γ st.k) ≤ uint.Z (ciEff γ st''.k) := by
                rw [Hst''.2]
                rcases hci' with ⟨-, hc⟩ | hc
                · rw [hc]; exact Int.le_refl _
                · rw [hc]; omega
              have h0 : (0 : Int) ≤ uint.Z γr.raft.ai0 := by word
              have := uint_nat_eq ai'
              omega
            have hgai : g' = ai' := by
              rw [ghostOf_past rp _ hW] at hg'
              simp only [List.length_append] at hg'; push_cast at hg'
              word
            ihave #Hlog'' : appliedLogAt γr ai' x'.log $$ []
            · rw [← hgai]; iexact Hlog'
            rw [ghostOf_past rp _ hW, srvRestRM_past C.isOn E γr rp _ hW]
            have hciE : ciEff γ st''.k = ai' := by
              rw [← Hst''.2] at hciL0
              word
            have hlenZ : uint.Z ai' = ((A ++ unapplied ai ms).length : Int) := by
              have := uint_nat_eq ai'; omega
            have hpos : 0 < uint.Z ai' := Int.lt_of_lt_of_le Hsnp hsentLe
            (try wp_auto)
            -- (with auth on) the apply thread's compaction revision `-1`, for the image's certificate
            imod srvApplyKVC_crev C s γ ci TM E ρ γr ρ.wait x' sa' $$ Hsrv HKV with ⟨HKV, %Hcr⟩
            -- (S2's `mergedCreate_window`) the commit's and the snapshot's contracts
            icases srvApplyKVC_coreA C s E ρ.wait x' sa' $$ HKV with ⟨%ua, HKVc, HAr, HKVk⟩
            -- the component lends its buckets to the window (none off)
            icases kvAppliedM_rev C.isOn γr (A ++ unapplied ai ms) x' sa' $$ Hka with ⟨Hka, %hrevC⟩
            ihave HL := acRes_lend C s E ua sa' hM hrevC $$ HAr
            icases Hkv with ⟨%kv, #Hkvf, #Hkvi, -⟩
            -- the apply goroutine's tokens (`apply.applyTok`), lent to the commit
            ihave HthT : apply.applyTok (GF := GF) E $$ [Hmr]
            · iunfold apply.applyTok; iexact Hmr
            -- (auth-lease S3a §5) the window at the mode's table
            ihave HRS : srvRestM E.authOn E γr (A ++ unapplied ai ms) $$ [HRS]
            · rw [hon]; iexact HRS
            imod mergedCreate_window hsh hPers hReach hImg hSnap hOn hSave hPut hUR hID hName hSafe C.isOn
                s γ ci TM E ρ γr b st'' ai' a' t' (A ++ unapplied ai ms) x' ρ.wait γp ua kv Hst''.1
                (acBkts C) (acImg C sa') (acRes C s E ua sa') (acBkts_rest C)
              $$ [Hst Hbe Happ HKVc HRS Hr1 Hl1 HthT HL]
              with ⟨%be, %dq, %RC, %RC', %RS, %RS', %Qd, Hkc, HRC, Hbeo, Hbs, HRCS, Hback⟩
            · iframe Hpkg Hsrv Hkvf Hkvi HW Hr1 Hl1 HthT Hst Hbe Happ HKVc HRS HL
            -- (2026-11-06, `notes/begin-tok-plan.md`) the apply thread's token (`srvGoRes`'s) pays for
            -- the snapshot's reader slot; the reader goroutine's fork token comes back
            iunfold srvGoRes at Hgr
            icases Hgr with ⟨HgrW, HgT⟩
            -- (raft-entsize [r3c]) the voters' conf state (the applied log is not empty)
            ihave #Hcv0 : epCsCfg γr cs' $$ []
            · icases Hecs with (%H0 | #H)
              · exfalso; omega
              · iexact H
            iunfold epCsCfg at Hcv0
            wp_apply (hCMpast s m sm at' ai' (ciEff γ st''.k) terms boot cs' sv.lg kv be dq RC RC' RS RS' Qd γr.raft hnl hsz20
              (by have h := Hsh.1.2.2.2.2.2.2.1 (Or.inr (Or.inr Hty)); exact ⟨h.1, h.2, Hsh.1.2.2.2.2.2.2.2⟩))
              $$ [Hlr Hkc HRC Hbeo Hbs HRCS Hm HgT]
              as %mg ⟨Hlr, HRS', Hbeo, HgT, %rc, %D, %c, #Hmg, #Hml, #HszC, #Hcso, %Hcml, Hrs, HQd⟩
            · iframe #; iframe Hlr Hkc HRC Hbeo Hbs HRCS Hm HgT
            ihave Hgr : srvGoRes s $$ [HgrW HgT]
            · iunfold srvGoRes; iframe HgrW HgT
            imod Hback $$ %D HRS' HQd Hbeo with ⟨%st3, HthT, Hst, Hbe, Happ, HKVc, HRS, #Hmimg, HAr, %Hst3⟩
            simp only [hciE]
            ihave HRS : srvRestM C.isOn E γr (A ++ unapplied ai ms) $$ [HRS]
            · rw [← hon]; iexact HRS
            ihave HKV := HKVk $$ HKVc HAr
            iunfold apply.applyTok at HthT
            irename HthT => Hmr
            -- the merged message sent: of a term committed through the applied index (the batch's
            -- term, `rnRtOk`; not `0`, a `MsgSnap`'s term), certified at the voters' conf state
            iunfold rnRtOk at Hrt
            rw [hγn]
            icases Hrt with (%Hrt0 | ⟨%ct, #Hct, %Hnct, %HbootCt, #Hbatch⟩)
            · exfalso
              exact (Hsh.1.2.2.2.1 (by rw [Hty]; simp [MsgSnap, MsgProp, MsgReadIndex,
                MsgTransferLeader])) Hrt0
            ihave #Hecs' : epCsCfg γr cs' $$ []
            · icases Hecs with (%H0 | #H)
              · exfalso; omega
              · iexact H
            iunfold epCsCfg at Hecs'
            iunfold epCsVoters at Hecs'
            icases Hecs' with ⟨%c0, #Hc0, %Hcs0⟩
            ihave %Hcc := csOpt_agree cs' c c0 $$ [Hcso Hc0]
            · iframe Hcso Hc0
            subst Hcc
            ihave %h61 := srvFrozenTerm_bound γs ai' at' $$ Hft
            imod srv_merged_sent γr (A ++ unapplied ai ms) ai' at' c γn.id ct sm sn hpos h61 hsz hlenZ
                hltA Hcs0 Hty hsn hsentLe (by have := hnA; have := uint_nat_eq ai'; omega)
              $$ [Hrli' HlbB Hsm Hct] with #Hsm'
            · iframe Hrli' HlbB Hsm Hct
            -- (`merged_imageC`) the image's certificate: the component's buckets the lent part's
            ihave Hmi : |={⊤}=> kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 (A ++ unapplied ai ms) x' sa' ∗
                □ (srvNet (GF := GF) γr.raft.raft).img ai' D $$ [Hka]
            · iapply (merged_imageC C s γ ci TM E ρ γr ai' (A ++ unapplied ai ms) x' sa' D hM hlenZ
                Hkv0 Hcr)
              iframe Hsrv Hka Hmimg
              ipureintro; exact Hst3.1
            imod Hmi with ⟨Hka, #Himg⟩
            imod srvMerged_bundle γr.raft.raft m rc sm γn.id c ai' at' D Hty
              $$ [Hml HszC Hsm' Hrs Himg] with Hbun
            · iframe Hml HszC Hsm' Hrs Himg
            (try wp_auto)
            wp_apply (hSMS s mg m rc sv.lg sv.memberID stg tr γN SN TSN lid) $$ [Hgr Hlr Hbun]
              as ⟨Hgr, Hlr⟩
            · iframe #; iframe Hgr Hlr; rw [HγN]; iframe Hbun
            (try wp_auto)
            have hF3 : loopOk γ st3 ai' ∧ ciEff γ st3.k = ciEff γ st'.k :=
              ⟨Hst3.2.1, by rw [Hst3.2.2]; exact Hst''.2⟩
            iapply Hfin $$ %st3 %hF3 Hai Hat Hcs Hst Hbe Happ Hlr Hgr Hmr HKV Hka HRS Hcursor HbootField Hao
          · have hahead : uint.Z ai' < uint.Z (ciEff γ st''.k) := by omega
            have hpos : 0 < uint.Z ai' := Int.lt_of_lt_of_le Hsnp hsentLe
            have hprev : uint.Z (ciEff γ st''.k) = uint.Z (ciEff γ st.k) := by
              rw [Hst''.2] at hahead ⊢
              rcases hci' with ⟨_, he⟩ | he
              · rw [he]
              · omega
            have hw : (A ++ unapplied ai ms).length < rp.A₀.length := by omega
            have hpfx : A ++ unapplied ai ms <+: rp.A₀ := by
              rcases hcmp with h | h
              · exact h
              · have := h.length_le; omega
            have hghost := ghostOf_in rp _ hpfx
            have hciLen : uint.Z (ciEff γ st''.k) = rp.A₀.length := by omega
            iunfold rnRtOk at Hrt
            icases Hrt with (%hzero | ⟨%ct, #Hct, -, %hbootCt, -⟩)
            · exfalso
              exact (Hsh.1.2.2.2.1 (by rw [Hty]; simp [MsgSnap, MsgProp, MsgReadIndex,
                MsgTransferLeader])) hzero
            have hdurableCommit : uint.Z (ciEff γ st''.k) ≤ uint.Z ct := by
              rw [hbootLog] at hbootCt
              omega
            rw [hghost, srvRestRM_in C.isOn E γr rp _ hw]
            imod srvApplyKVC_crev C s γ ci TM E ρ γr ρ.wait x' sa' $$ Hsrv HKV with ⟨HKV, %Hcr⟩
            icases srvApplyKVC_coreA C s E ρ.wait x' sa' $$ HKV with ⟨%ua, HKVc, HAr, HKVk⟩
            icases kvAppliedM_rev C.isOn γr rp.A₀ x' sa' $$ Hka with ⟨Hka, %hrevC⟩
            ihave HL := acRes_lend C s E ua sa' hM hrevC $$ HAr
            icases Hkv with ⟨%kv, #Hkvf, #Hkvi, -⟩
            ihave HthT : apply.applyTok (GF := GF) E $$ [Hmr]
            · iunfold apply.applyTok; iexact Hmr
            ihave HRS : srvRestRpM E.authOn E γr rp.A₀ (restReplay γr rp (A ++ unapplied ai ms)) $$ [HRS]
            · rw [hon]; iexact HRS
            imod mergedCreate_window_replay hsh hPers hReach hImg hSnap hOn hSave hPut hUR hID hName hSafe
                C.isOn s γ ci TM E ρ γr b st'' ai' a' t' rp.A₀ x' ρ.wait γp ua kv _
                (restReplay_bk γr rp _) Hst''.1 (acBkts C) (acImg C sa') (acRes C s E ua sa') (acBkts_rest C)
              $$ [Hst Hbe Happ HKVc HRS Hr1 Hl1 HthT HL]
              with ⟨%be, %dq, %RC, %RC', %RS, %RS', %Qd, Hkc, HRC, Hbeo, Hbs, HRCS, Hback⟩
            · iframe Hpkg Hsrv Hkvf Hkvi HW Hr1 Hl1 HthT Hst Hbe Happ HKVc HRS HL
            iunfold srvGoRes at Hgr
            icases Hgr with ⟨HgrW, HgT⟩
            ihave #Hcv0 : epCsCfg γr cs' $$ []
            · icases Hecs with (%hzero | #H)
              · exfalso; omega
              · iexact H
            iunfold epCsCfg at Hcv0
            let durableTerm := (rp.A₀.getLast?.map EntryModel.term).getD (W64 0)
            have hlast : lastTermIs rp.A₀ durableTerm := by
              cases h : rp.A₀.getLast? with
              | none => exact Or.inl (List.getLast?_eq_none_iff.mp h)
              | some e => exact Or.inr (by simp [durableTerm, h])
            ihave #Hboot : epCsVoters γr.raft boot $$ []
            · icases HbootCfg with (%h | #H)
              · exfalso; simp only [List.length_append] at hw; omega
              · iexact H
            ihave %hboot : ⌜boot ≠ null⌝ $$ []
            · iunfold epCsVoters at Hboot
              icases Hboot with ⟨%c, #Hpts, -⟩
              iunfold csPts at Hpts
              iNamed Hpts
              ipureintro; exact Hnn
            iunfold rnReplayJob at Hjob
            ihave Hhist := Hjob $$ %sm %(ciEff γ st''.k) %(by rw [hbootLog]; exact ⟨Hty, rfl, by omega, hciLen⟩)
            rw [hγn, hbootLog]
            ihave Hhist' := Hhist $$ Hsm %m Hsrc
            imod Hhist' with ⟨%runs, %run, #Hruns, %hr⟩
            have hsend := hCM s m sm at' ai' (ciEff γ st''.k) durableTerm terms boot cs' sv.lg kv be dq
              RC RC' RS RS' Qd γr.raft hsz20
              (by have h := Hsh.1.2.2.2.2.2.2.1 (Or.inr (Or.inr Hty)); exact ⟨h.1, h.2, Hsh.1.2.2.2.2.2.2.2⟩)
            simp only [hahead, ↓reduceIte] at hsend
            (try wp_auto)
            wp_apply hsend $$ [Hlr Hkc HRC Hbeo Hbs HRCS Hm HgT]
              as %mg ⟨Hlr, HRS', Hbeo, HgT, %rc, %D, %c, #Hmg, #Hml, #HszC, -, %hconf, %hsize, Hrs, HQd⟩
            rotate_left
            · ihave Hgr : srvGoRes s $$ [HgrW HgT]
              · iunfold srvGoRes; iframe HgrW HgT
              imod Hback $$ %D HRS' HQd Hbeo with ⟨%st3, HthT, Hst, Hbe, Happ, HKVc, HRS, #Hmimg, HAr, %Hst3⟩
              ihave HRS : srvRestRpM C.isOn E γr rp.A₀ (restReplay γr rp (A ++ unapplied ai ms)) $$ [HRS]
              · rw [← hon]; iexact HRS
              ihave HKV := HKVk $$ HKVc HAr
              iunfold apply.applyTok at HthT
              irename HthT => Hmr
              imod srv_merged_sent γr rp.A₀ (ciEff γ st''.k) durableTerm c γn.id ct sm sn (by omega)
                  (by omega) hsz hciLen hlast hconf Hty hsn (by omega) hdurableCommit
                  $$ [Hrli' HlbDisk Hsm Hct] with #Hsent
              · iframe Hrli' HlbDisk Hsm Hct
              ihave Hmi : |={⊤}=> kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 rp.A₀ x' sa' ∗
                  □ (srvNet (GF := GF) γr.raft.raft).img (ciEff γ st''.k) D $$ [Hka]
              · iapply merged_imageC C s γ ci TM E ρ γr (ciEff γ st''.k) rp.A₀ x' sa' D hM hciLen Hkv0 Hcr
                iframe Hsrv Hka Hmimg
                ipureintro; exact Hst3.1
              imod Hmi with ⟨Hka, #Himg⟩
              imod srvMerged_bundle γr.raft.raft m rc sm γn.id c (ciEff γ st''.k) durableTerm D Hty
                $$ [Hml HszC Hsent Hrs Himg] with Hbun
              · iframe Hml HszC Hsent Hrs Himg
              (try wp_auto)
              wp_apply (hSMS s mg m rc sv.lg sv.memberID stg tr γN SN TSN lid) $$ [Hgr Hlr Hbun] as ⟨Hgr, Hlr⟩
              · iframe #; iframe Hgr Hlr; rw [HγN]; iframe Hbun
              (try wp_auto)
              have hF3 : loopOk γ st3 ai' ∧ ciEff γ st3.k = ciEff γ st'.k :=
                ⟨Hst3.2.1, by rw [Hst3.2.2]; exact Hst''.2⟩
              iapply Hfin $$ %st3 %hF3 Hai Hat Hcs Hst Hbe Happ Hlr Hgr Hmr HKV Hka HRS Hcursor HbootField Hao
            · iframe #; iframe Hlr Hkc HRC Hbeo HRCS Hm HgT
              iunfold srvBeSnapOk at Hbs
              iunfold srvBeSnapOk
              icases Hbs with ⟨%bi, %hb, #Hsnap⟩
              iexists bi
              isplitr; · ipureintro; exact hb
              iintro !> %Ψ Hpre HΨ
              wp_apply Hsnap $$ [Hpre] as %sp %D ⟨Hopen, Hrs, HQ, %hm⟩
              · iexact Hpre
              iapply HΨ $$ %sp %D
              dsimp only
              iframe Hopen Hrs HQ
              obtain ⟨stored, hmeta⟩ := hm
              iexists stored
              isplitr; · ipureintro; exact hmeta
              iintro _
              iunfold replayImageMetadata
              iexists true
              simp only [hboot, ↓reduceIte]
              isplitr
              · iexists runs; iframe Hruns; ipureintro; exact hr.1
              iframe Hboot
              iunfold replaySnapshotTerm
              simp only [↓reduceIte]
              iexists runs, run
              iframe Hruns
              ipureintro; exact hr.2
        · (try wp_auto)
          wp_apply (hGTo.1 m (DFrac.own 1) DFrac.discard false sm) $$ [Hm] as Hm
          · iframe #; iframe Hm
          (try wp_auto)
          wp_apply (hRSn γb s sm.msg.To' (W64 2)) $$ []
          · iframe #
          (try wp_auto)
          iapply Hfin $$ %st'' %Hst'' Hai Hat Hcs Hst Hbe Happ Hlr Hgr Hmr HKV Hka HRS Hcursor HbootField Hao
      · itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- `default`
    (try wp_auto)
    iapply Hfin $$ %st'' %Hst'' Hai Hat Hcs Hst Hbe Happ Hlr Hgr Hmr HKV Hka HRS Hcursor HbootField Hao

set_option maxRecDepth 100000 in
/-- **`applyAll.spec`** (the auth component's stage 2, 2026-11-04: in both auth modes): the batch
(`wp_proofBatch`, the restart form since R2d'a's swap batch 3) and the snapshot payload in the server's mode (`wp_proofSnapM`; until R2d'a's swap
batch 2, 2026-11-06, from the off case `wp_proofSnap`). -/
theorem EtcdServer.applyAll.wp_proof
    (hASnap : EtcdServer.applySnapshot.spec (GF := GF) (hG := hG))
    (hAE : EtcdServer.applyEntries.spec (GF := GF) (hG := hG))
    (hBk : EtcdServer.Backend.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hV : backend.VerifyBackendConsistency.spec (GF := GF) (hG := hG))
    (hSINC : EtcdServer.snapshotIfNeededAndCompactRaftLog.spec (GF := GF) (hG := hG))
    (hGT : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (hCM : EtcdServer.createMergedSnapshotMessage.spec (GF := GF) (hG := hG))
    (hSMS : EtcdServer.sendMergedSnap.spec (GF := GF) (hG := hG))
    -- A stale-term request still reports its failure to Raft.
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
    EtcdServer.applyAll.spec (GF := GF) (hG := hG) :=
  ⟨EtcdServer.applyAll.wp_proofBatch hASnap hAE hBk hLg hV hSINC hGT hCM hSMS hGTo hRSn hsh hPers hReach hImg hSnap hOn hSave
      hPut hUR hID hName hSafe,
    EtcdServer.applyAll.wp_proofSnapM hASnap.2.1 hAE.2 hBk hLg hV hSINC.2 hGT (EtcdServer.createMergedSnapshotMessage.caughtUp_of_spec hCM) hSMS hGTo hRSn hsh hPers hReach hImg hSnap hOn hSave hPut hUR hID hName
      hSafe⟩

end proof

end EtcdGrove
end Perennial
