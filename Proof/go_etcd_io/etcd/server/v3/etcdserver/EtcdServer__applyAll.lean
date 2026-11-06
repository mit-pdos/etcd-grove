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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapSendBranch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyAllSnap
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.MergedImageOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyAllSnapOn

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
/-- **The merged `applyAll.specBatch` at no window** (R2d: until then `wp_proofBatch`; the auth component's stage 2c, 2026-11-04; until then
`wp_proofBatch` off and `wp_proofOn` on): one proof over the slot `C`, its rows at the mode's
(`AuthCompRows`' bridges), the callees' specs over the environment's mode (`E.authOn = C.isOn`),
the merged snapshot's window lent the component's buckets (`acRes_lend`; none off) and its image
certified by `merged_imageC`. -/
theorem EtcdServer.applyAll.wp_proofBatchNoWin
    (hASnap : EtcdServer.applySnapshot.spec (GF := GF) (hG := hG))
    (hAE : EtcdServer.applyEntries.spec (GF := GF) (hG := hG))
    (hBk : EtcdServer.Backend.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hV : backend.VerifyBackendConsistency.spec (GF := GF) (hG := hG))
    (hSINC : EtcdServer.snapshotIfNeededAndCompactRaftLog.spec (GF := GF) (hG := hG))
    -- (2026-10-31, S1) the merge branch: the message's getters, the merge, the send, and what
    -- the snapshot window takes (`mergedCreate_window`)
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
    EtcdServer.applyAll.specBatchNoWin (GF := GF) (hG := hG) := by
  intro s γ ci TM C E ρ γr b ep ap es ents ms f0 rac nc st ai at0 a t cs x sa A mst γs γp dv γnc w nk
    q γn rt n
  simp only [srvRunH_noWin]
  wp_start as ⟨%hP, #HsrvC, #Hlnil, #Hsa, #Hbw, #Hes, #Hrac, #Hracc, #Hsn, #Hnc, #Hncb, Hnrc, #Hesl, #Hentsat, Hai, Hat, Hcs, #Hcv,
    Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, HKV, Hao, #Hlog, #Hbc, #HW, #HWA, Hka, HRS, #Hkb, Hdv, #Hdvr, HAR, Hrun, #Hsd, #Hkv, #Hmsi, HwalT, #Hrtf, #Hrt, Hso, HtokR⟩
  obtain ⟨hM, hRB, Hms, Hai1, Hok, hEok, hdv, hAL, hAT, Hdisk, hciA, hcia, hγn, hpre, hnA⟩ := hP
  have hon : E.authOn = C.isOn := by rw [apply.AEnv.authOn_eq, hM, AuthC.mode_isOn]
  -- (the auth component's stage 2c) the slot's rows at the mode's
  ihave #Hsrv := (isServerM_C C s γ ci TM E ρ γr).2 $$ HsrvC
  ihave #HlnilM : srvLessorNilM C.isOn s $$ []
  · rw [srvLessorNilM_eq]; iexact Hlnil
  ihave HKV := (srvApplyKVM_C C s E ρ.wait x sa).2 $$ HKV
  ihave HtokR : srvTokRights E (ciEff γ st.k) $$ [HtokR]
  · rw [srvTokRights_eq C E _ hM]; iexact HtokR
  icases srvApRes_cfg_size s γr A $$ HAR with ⟨HAR, %hsz⟩
  ihave #Hsrv' := Hsrv
  iunfold isServerM at Hsrv'
  icases Hsrv' with ⟨%Hρrd, -, ⟨%sv, #Hfl⟩, -, -, #HrnS, -⟩
  iunfold srvFieldsAtM at Hfl
  icases Hfl with ⟨#Hlgf, %Hlgnn, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, -⟩
  ihave #Hsa' := Hsa
  iunfold isServerApplyAll at Hsa'
  icases Hsa' with ⟨%wt, %msc, %sc, #Hwtf, #Hwt, #Hmscf, ⟨%γm, %Hγm, #Hmscb⟩, #Hsc,
    ⟨%stg, #Hstgf, #Hstgc⟩, -, #Hinf, -, ⟨%tr, %γN, %lid, %SN, %TSN, #Htrf, #Htr, %HγN⟩, %Hkv0⟩
  ihave #HstgS := Hstgc
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, ⟨%g, #Hg, #Hgs⟩, ⟨%bsl, #Hbsl⟩, -⟩
  ihave #Pbe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
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
  have hAE1 := EtcdServer.applyEntries.specBatch_noWin hAE.1 s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr A γp dv w sa
    (by rw [hM]; cases C <;> simp [AuthC.mode])
    (fun h => by rw [hon] at h; cases C <;> simp_all [AuthC.isOn, acReceiptOk]) Hms Hai1 Hok
    (by rw [hon]; exact hEok) hdv
  try simp only [srvRunH_noWin] at hAE1
  rw [hon] at hAE1
  wp_apply hAE1
    $$ [Hai Hat Hcs Hcv Hst Hbe Happ Hlr Hgr HKV Hao Hfs Hka HRS Hdv Hrun HAR HtokR]
    as ⟨Hfs, Hdv, Hrun, HAR, %st', %ai', %at', %a', %t', %cs', Hai, Hat, Hcs, #Hcv', Hst, HtokR, Hbe, Happ, Hlr, Hgr, Hao, #HWA',
      ⟨%x', %sa', HKV, %Hx', #Hlog', Hka, HRS⟩, %Hpost⟩
  · iframe #; iframe
  iunfold srvFS at Hfs
  icases Hfs with ⟨%sf1, Hsf1⟩
  obtain ⟨hok', hai', hlen', hci', hat'⟩ := Hpost
  have hciL : uint.Z ai ≤ uint.Z (ciEff γ st.k) → uint.Z ai' ≤ uint.Z (ciEff γ st'.k) := by
    intro h
    rcases hci' with ⟨hun, hc⟩ | hc
    · rw [hun, List.length_nil] at hlen'; rw [hc]; omega
    · rw [hc]; omega
  have Hai' : uint.Z ai ≤ uint.Z ai' := by rw [hai']; exact Int.le_max_left _ _
  -- (D22 J1b) the snapshot resources at the new applied index
  ihave Hso := srvSnapOwn_mono s ci E γr _ ai ai' Hai' $$ Hso
  ihave Hss : srvSnapState s ep mst γs ai' (W64 0) $$ [Hsd0 Hsm0 Hsf1]
  · iunfold srvSnapState; iexists _, _, _; iframe Hsd0 Hsm0 Hsf1 Hmst Hslb0
    ipureintro; exact ⟨by have := Hdm0.1; omega, by have := Hdm0.2; omega⟩
  (try wp_auto)
  -- `backend.VerifyBackendConsistency(s.Backend(), s.Logger(), true, schema.AllBuckets...)`
  wp_apply hBk s E.γbe $$ [Hbr] as %be ⟨Hbr, -⟩
  · iframe #; iframe Hbr
  wp_apply hLg s sv.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hV be sv.lg true bsl
  (try wp_auto)
  -- `proposalsApplied.Set(float64(ep.appliedi))`
  iunfold gaugeSetSpec at Hgs
  wp_apply Hgs
  (try wp_auto)
  -- `s.applyWait.Trigger(ep.appliedi)`: the waiters through `ai'`
  icases srvAppliedOwn_lb γr ai' $$ Hao with ⟨Hao, #Hlb⟩
  iunfold isWaitTime at Hwt
  icases Hwt with ⟨%wi, %Hwi, -, #HTrig⟩
  subst Hwi
  wp_apply HTrig $$ []
  · iintro !>; iexact Hlb
  (try wp_auto)
  -- `<-apply.notifyc`: (D43 M3) the view after the batch deposited
  wp_apply wp_notify_receive γnc nc _ $$ [Hnrc Hdv]
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
      iexists γ, TM, E, b, st', ai', at', a', t', cs'
      iframe HsrvC Hlnil
      isplitr
      · ipureintro; exact beSucc_refl γ E
      iframe Hai Hat Hcs Hcv' Hss Hst HtokR Hbe Happ Hlr Hgr Hbr HAR Hrun
      isplitl [Hao]
      · iexact Hao
      isplitr
      · iexact Hlb
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
      ipureintro; exact ⟨hok', hai', hci'.imp_left And.right, hciL, hat'⟩
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
  iunfold kvBatch at Hkb'
  icases Hkb' with ⟨#HlbB, -⟩
  ihave Hstor : srvSnapStor mst γs γr nk ai' at' $$ []
  · iunfold srvSnapStor
    iframe Hmsi
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
      iapply epCsAt_ne _ _ _ hL $$ Hcv'
  -- `s.snapshotIfNeededAndCompactRaftLog(ep)`
  have hS1 := hSINC.1 s E ρ.wait γ ci b γr ep st' ai' at' cs' a' t' x' mst γs nk γp
    (w + (unapplied ai ms).length) TM ρ sa' q γn
  rw [hon] at hS1
  wp_apply hS1 hok'
      (hciL hciA) Hdisk.2.1.2.2.1 hsz Hdisk.2.2.1 hγn hpre
    $$ [Hss Hai Hat Hcs Hst Hbe Happ Hlr HKV HwalT Hstor]
    as ⟨%st'', Hss, -, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, HwalT, %Hst''⟩
  · iframe #; iframe
  (try wp_auto)
  ihave HKV := (srvApplyKVM_C C s E ρ.wait x' sa').1 $$ HKV
  iunfold epConfState at Hcs
  icases Hcs with ⟨Hcs, #Hcsok⟩
  -- (2026-10-31, S1) the step's end, shared by the select's branches: the apply thread at a state
  -- `stF` of the same consistent index
  ihave Hfin : iprop(∀ stF : ApplyState, ⌜loopOk γ stF ai' ∧ ciEff γ stF.k = ciEff γ st'.k⌝ -∗
      epAppliedIAddr ep ↦ ai' -∗ epAppliedTAddr ep ↦ at' -∗ epConfStateAddr ep ↦ cs' -∗
      applyThread γ stF -∗ applyBackend γ ci b -∗ ciApplying ci a' t' -∗ srvLgReader s -∗
      srvGoRes s -∗ srvApplyKVC C s E ρ.wait x' sa' -∗
      kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 (A ++ unapplied ai ms) x' sa' -∗
      srvRest E γr (A ++ unapplied ai ms) -∗ Φ #()) $$ [HΦ Hss Hbr HAR Hrun Hao HwalT HtokR Hso]
  · iintro %stF %HF Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka HRS
    ihave Hcs : epConfState ep cs' $$ [Hcs]
    · iunfold epConfState; iframe Hcs Hcsok
    ihave HtokR : acTok C (ciEff γ stF.k) $$ [HtokR]
    · rw [HF.2, ← srvTokRights_eq C E _ hM]; iexact HtokR
    iapply HΦ
    iexists γ, TM, E, b, stF, ai', at', a', t', cs'
    iframe HsrvC Hlnil
    isplitr
    · ipureintro; exact beSucc_refl γ E
    iframe Hai Hat Hcs Hcv' Hss Hst HtokR Hbe Happ Hlr Hgr Hbr HAR Hrun
    isplitl [Hao]
    · iexact Hao
    isplitr
    · iexact Hlb
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
    exact ⟨HF.1, hai', by rw [HF.2]; exact hci'.imp_left And.right, by rw [HF.2]; exact hciL, hat'⟩
  -- `select { case m := <-s.r.msgSnapC: ...; default: }` (2026-10-31, S1: a `MsgSnap` raft handed
  -- out, merged with the backend's image and sent when the guard holds)
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
        icases HP with ⟨%sm, Hm, %Hty, #Hsm, -⟩
        rw [Hγm]
        letI := srvStor (GF := GF) γr.raft.raft
        ihave %Hsh := sentMsg_shape _ _ _ _ $$ Hsm
        obtain ⟨sn, hsn, -⟩ := Hsh.2 Hty
        ihave %Hsnp := srv_sentSnap_pos γr γm.id sm sn Hty hsn $$ [Hrli' Hsm]
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
            have HifI := Hif
            have hciE : ciEff γ st''.k = ai' := by
              rw [Hst''.2]
              have h1 := hciL hciA
              have h2 : uint.Z (ciEff γ st'.k) ≤ uint.Z ai' := by
                rcases hci' with ⟨-, hc⟩ | hc
                · rw [hc]; omega
                · rw [hc]; have := hcia; have := Hai'; omega
              word
            have hlenZ : uint.Z ai' = ((A ++ unapplied ai ms).length : Int) := by
              have := uint_nat_eq ai'; omega
            have hpos : 0 < uint.Z ai' := by word
            (try wp_auto)
            -- (S2's `mergedCreate_window`) the commit's and the snapshot's contracts
            icases srvApplyKVC_coreA C s E ρ.wait x' sa' $$ HKV with ⟨%ua, HKVc, HAr, HKVk⟩
            -- the component lends its buckets to the window (none off)
            ihave HL := acRes_lend C s E ua sa' hM $$ HAr
            icases Hkv with ⟨%kv, #Hkvf, #Hkvi⟩
            imod mergedCreate_window hC hSnap hOn hSave hPut hUR hID hName hSafe C.isOn s γ ci TM E ρ
                γr b st'' ai' a' t' (A ++ unapplied ai ms) x' ρ.wait γp ua kv Hst''.1 hciE hpos hlenZ
                (acBkts C) (acImg C sa') (acRes C s E ua sa') (acBkts_rest C)
              $$ [Hst Hbe Happ HKVc HRS Hr1 Hl1 Hr2 Hl2 HL]
              with ⟨%be, %dq, %RC, %RC', %RS, %RS', Hkc, HRC, Hbeo, Hbs, HRCS, Hback⟩
            · iframe Hpkg Hsrv Hkvf Hkvi HW Hlog' HlbB Hr1 Hl1 Hr2 Hl2 Hst Hbe Happ HKVc HRS HL
            wp_apply (hCM s m sm at' ai' cs' sv.lg kv be dq RC RC' RS RS' _)
              $$ [Hlr Hkc HRC Hbeo Hbs HRCS Hm]
              as %mg ⟨Hlr, HRS', Hbeo, %rc, %D, %c, #Hmg, #Hml, #Hcso, Hrs, %HQd⟩
            · iframe #; iframe Hlr Hkc HRC Hbeo Hbs HRCS Hm; ipureintro; exact Hlgnn
            imod Hback $$ HRS' Hbeo with ⟨%st3, Hst, Hbe, Happ, HKVc, HRS, HAr, %Hst3⟩
            ihave HKV := HKVk $$ HKVc HAr
            icases srvApplyKVC_idxCert C s E ρ.wait x' sa' $$ HKV with ⟨HKV, #Hicx⟩
            ihave #Hrcx := mvcc.idxCert_rcpt E.γ.idx x'.log $$ Hicx
            -- the merged message sent: of a term committed through the applied index (the batch's
            -- term, `rnRtOk`; not `0`, a `MsgSnap`'s term), certified at the voters' conf state
            iunfold rnRtOk at Hrt
            rw [hγn]
            icases Hrt with (%Hrt0 | ⟨%ct, #Hct, %Hnct⟩)
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
            imod srv_merged_sent γr (A ++ unapplied ai ms) ai' at' c γm.id ct sm sn hpos h61 hsz hlenZ
                hltA Hcs0 Hty hsn (by word) (by have := hnA; have := uint_nat_eq ai'; omega)
              $$ [Hrli' HlbB Hsm Hct] with #Hsm'
            · iframe Hrli' HlbB Hsm Hct
            -- (`merged_imageC`) the image's certificate: the component's buckets the lent part's
            ihave Hmi : |={⊤}=> kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 (A ++ unapplied ai ms) x' sa' ∗
                □ (srvNet (GF := GF) γr.raft.raft).img ai' D $$ [Hka]
            · iapply (merged_imageC C s γ ci TM E ρ γr ai' (A ++ unapplied ai ms) x' sa' D hM hlenZ
                Hkv0)
              iframe Hsrv Hka Hrcx; ipureintro; exact HQd
            imod Hmi with ⟨Hka, #Himg⟩
            imod srvMerged_bundle γr.raft.raft m rc sm γm.id c ai' at' D Hty
              $$ [Hml Hsm' Hrs Himg] with Hbun
            · iframe Hml Hsm' Hrs Himg
            (try wp_auto)
            wp_apply (hSMS s mg m rc sv.lg sv.memberID stg tr γN SN TSN lid) $$ [Hgr Hlr Hbun]
              as ⟨Hgr, Hlr⟩
            · iframe #; iframe Hgr Hlr; rw [HγN]; iframe Hbun; ipureintro; exact Hlgnn
            (try wp_auto)
            have hF3 : loopOk γ st3 ai' ∧ ciEff γ st3.k = ciEff γ st'.k :=
              ⟨Hst3.1, by rw [Hst3.2]; exact Hst''.2⟩
            iapply Hfin $$ %st3 %hF3 Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka HRS
          · (try wp_auto)
            iapply Hfin $$ %st'' %Hst'' Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka HRS
        · (try wp_auto)
          iapply Hfin $$ %st'' %Hst'' Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka HRS
      · itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- `default`
    (try wp_auto)
    iapply Hfin $$ %st'' %Hst'' Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka HRS

/-! ### The window's list facts (R2d probe) -/

/-- The pending replays of a window over the ghost log `A` at Go's index `ai`: `A` is Go's log
and them. -/
private theorem winGhost_len (ai : w64) (A W : List EntryModel)
    (h : uint.Z (winGhost ai W) = A.length) (hs : W <:+ A) : A.length = uint.nat ai + W.length := by
  have hle := hs.length_le
  have hn := uint_nat_eq ai
  cases W with
  | nil => simp only [winGhost] at h; simp only [List.length_nil]; omega
  | cons w W' =>
    simp only [winGhost] at h
    have hb : uint.Z ai < 2 ^ 64 := by word
    have : uint.Z (W64 (uint.Z ai + ((w :: W').length : Int))) =
        (uint.Z ai + ((w :: W').length : Int)) % 2 ^ 64 := by word
    rw [this] at h
    have hz : 0 ≤ uint.Z ai := by word
    omega

/-- A batch starting with the pending replays is a prefix of them and its new entries. -/
private theorem winAgree_prefix : ∀ (W ms : List EntryModel), winAgree W ms → ms <+: W ++ winNew W ms
  | [], ms, _ => by simp only [winNew, List.nil_append]; exact List.prefix_refl ms
  | _ :: _, [], _ => List.nil_prefix
  | w :: W, m :: ms, h => by
      obtain ⟨rfl, h⟩ := h
      show w :: ms <+: w :: (W ++ winNew W ms)
      exact List.cons_prefix_cons.2 ⟨rfl, winAgree_prefix W ms h⟩

/-- A batch's new entries and the replays left: the batch and the pending replays. -/
private theorem winNew_rest_len {α : Type} : ∀ (W ms : List α),
    (winNew W ms).length + W.length = ms.length + (winRest W ms).length
  | [], ms => by simp [winNew, winRest]
  | _ :: _, [] => by simp [winNew, winRest]
  | _ :: W, _ :: ms => by
      have := winNew_rest_len W ms
      show (winNew W ms).length + (W.length + 1) = ms.length + 1 + (winRest W ms).length
      omega

/-- A log consecutive from `a0` (w64 indices) is shorter than `2 ^ 64`. -/
private theorem idxOk_len_lt (a0 : w64) (G : List EntryModel) (h : srvIdxOkW a0 G) :
    (G.length : Int) < 2 ^ 64 := by
  cases hG : G.length with
  | zero => simp
  | succ k =>
    have hk : k < G.length := by omega
    have h1 := (h k (G[k]'hk) (List.getElem?_eq_getElem hk)).1
    have hb : uint.Z (G[k]'hk).index < 2 ^ 64 := by word
    have hz : 0 ≤ uint.Z a0 := by word
    omega

/-- The ghost index without overflow. -/
private theorem winGhost_Z {α : Type} (ai : w64) (R : List α) (h : uint.Z ai + R.length < 2 ^ 64) :
    uint.Z (winGhost ai R) = uint.Z ai + R.length := by
  cases R with
  | nil => simp [winGhost]
  | cons r R' => simp only [winGhost]; word

/-- A batch past every pending replay: its new entries are the rest of it. -/
private theorem winRest_nil_len {α : Type} : ∀ (W ms : List α), winRest W ms = [] →
    (winNew W ms).length + W.length = ms.length
  | [], ms, _ => by simp [winNew]
  | _ :: _, [], h => by simp [winRest] at h
  | _ :: W, _ :: ms, h => by
      have := winRest_nil_len W ms h
      show (winNew W ms).length + (W.length + 1) = ms.length + 1
      omega

/-- (Q16 (2)) **Go's applied log** after a batch (the ghost log's first `ai` entries and the batch)
is a prefix of the ghost log after it. -/
private theorem win_goLog_prefix (ai : w64) (A W ms : List EntryModel)
    (hlen : A.length = uint.nat ai + W.length) (hs : W <:+ A) (hag : winAgree W ms) :
    A.take (uint.nat ai) ++ ms <+: A ++ winNew W ms := by
  obtain ⟨t, rfl⟩ := hs
  have ht : t.length = uint.nat ai := by rw [List.length_append] at hlen; omega
  rw [List.take_left' ht, List.append_assoc]
  exact (List.prefix_append_right_inj t).2 (winAgree_prefix W ms hag)

/-- (Q17 F2) The pending replays, entries of the ghost log consecutive from `a0`, are at or below
its end `c`. -/
private theorem win_idx_le (a0 c : w64) (A X W : List EntryModel) (h : srvIdxOkW a0 (A ++ X))
    (hc : uint.Z c = uint.Z a0 + A.length) (hs : W <:+ A) :
    ∀ m ∈ W, uint.Z m.index ≤ uint.Z c := by
  intro m hm
  obtain ⟨n, hn⟩ := List.getElem?_of_mem (hs.subset hm)
  have hlt : n < A.length := (List.getElem?_eq_some_iff.1 hn).1
  have := (h n m (by rw [List.getElem?_append_left hlt]; exact hn)).1
  omega

section matcher
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
/-- `applyEntries.specBatch`'s (window form's) running-token match is `srvRunH`. -/
private theorem srvRunH_applyEntries_specW (γs : ServerRaftNames) (dv : Option Loc) :
    _root_.Perennial.EtcdGrove.EtcdServer.applyEntries.specBatch.match_1 (fun _ => IProp GF) dv
      (fun _ => iprop(True))
      (fun n => letI := srvStor (GF := GF) γs.raft; nodeRunning n γs.raft.cl srvClusterN (1 : Qp).half) =
      srvRunH γs dv := by
  cases dv <;> rfl
end matcher

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`applyAll.specBatch` in the replay window** (R2d, Q13 (a); DRAFT; the R2d probe, 2026-11-06:
proved over the callees' window forms but for the merged snapshot sent while the window is still
pending after the batch, `-- DRAFT (R2d-3m: merged send in a window)`; the no-window proof is
`wp_proofBatchNoWin`). Go's applied log after the batch (`take ai A ++ unapplied ai ms`, Q16 (2)) is
a prefix of the ghost log (`win_goLog_prefix`) and is what the local snapshot takes. -/
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
    EtcdServer.applyAll.specBatch (GF := GF) (hG := hG) := by
  intro s γ ci TM C E ρ γr b ep ap es ents ms f0 rac nc st ai at0 a t cs x sa A mst γs γp dv γnc w nk
    q γn rt n W D hwin
  simp only [srvRunH_applyAll_spec]
  wp_start as ⟨%hP, #HsrvC, #Hlnil, #Hsa, #Hnms, #Hbw, #Hes, #Hrac, #Hracc, #Hsn, #Hnc, #Hncb, Hnrc, #Hesl, #Hentsat, Hai, Hat, Hcs, #Hcv,
    Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, HKV, Hao, #Hlog, #Hbc, #HW, #HWA, Hka, HRS, #Hkb, Hdv, #Hdvr, HAR, Hrun, #Hsd, #Hkv, #Hmsi, HwalT, #Hrtf, #Hrt, Hso, HtokR⟩
  obtain ⟨hM, hRB, Hms, Hai1, Hok, hEok, hdv, hAL, hAT, Hdisk, hciA, hcia, hγn, hpre, hnA⟩ := hP
  have hon : E.authOn = C.isOn := by rw [apply.AEnv.authOn_eq, hM, AuthC.mode_isOn]
  -- (R2d) the window: the pending replays a suffix of the ghost log, which is Go's log and them
  have hWs : W <:+ A := (List.suffix_append D W).trans hwin.1
  have hAlen := winGhost_len ai A W hAL hWs
  have hciA0 : uint.Z ai ≤ uint.Z (ciEff γ st.k) := by
    have := hciA; have := hAL; have := uint_nat_eq ai; omega
  have hGoPre := win_goLog_prefix ai A W (unapplied ai ms) hAlen hWs hwin.2
  -- the batch's committed log (`kvBatchW`'s), and (F2) the pending replays at or below the
  -- consistent index: entries of the ghost log, consecutive from the start
  ihave #Hkb' := Hkb
  iunfold kvBatchW at Hkb'
  icases Hkb' with ⟨#HlbB, %hkbW⟩
  ihave %hidxG := srvRLogLb_idx _ _ $$ HlbB
  have hF2 : ∀ m ∈ W, uint.Z m.index ≤ uint.Z (ciEff γ st.k) :=
    win_idx_le γr.raft.ai0 (ciEff γ st.k) A _ W hidxG
      (by have := hkbW.1; have := hciA; have := hcia; omega) hWs
  -- (the auth component's stage 2c) the slot's rows at the mode's
  ihave #Hsrv := (isServerM_C C s γ ci TM E ρ γr).2 $$ HsrvC
  ihave #HlnilM : srvLessorNilM C.isOn s $$ []
  · rw [srvLessorNilM_eq]; iexact Hlnil
  ihave HKV := (srvApplyKVM_C C s E ρ.wait x sa).2 $$ HKV
  ihave HtokR : srvTokRights E (ciEff γ st.k) $$ [HtokR]
  · rw [srvTokRights_eq C E _ hM]; iexact HtokR
  icases srvApRes_cfg_size s γr A $$ HAR with ⟨HAR, %hsz⟩
  ihave #Hsrv' := Hsrv
  iunfold isServerM at Hsrv'
  icases Hsrv' with ⟨%Hρrd, -, ⟨%sv, #Hfl⟩, -, -, #HrnS, -⟩
  iunfold srvFieldsAtM at Hfl
  icases Hfl with ⟨#Hlgf, %Hlgnn, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, -⟩
  ihave #Hsa' := Hsa
  iunfold isServerApplyAll at Hsa'
  icases Hsa' with ⟨%wt, %msc, %sc, #Hwtf, #Hwt, #Hmscf, ⟨%γm, %Hγm, #Hmscb⟩, #Hsc,
    ⟨%stg, #Hstgf, #Hstgc⟩, -, #Hinf, -, ⟨%tr, %γN, %lid, %SN, %TSN, #Htrf, #Htr, %HγN⟩, %Hkv0⟩
  ihave #HstgS := Hstgc
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, ⟨%g, #Hg, #Hgs⟩, ⟨%bsl, #Hbsl⟩, -⟩
  ihave #Pbe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
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
  have hAE1 := hAE.1 s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr A γp dv w sa W D
    (by rw [hM]; cases C <;> simp [AuthC.mode])
    (fun h => by rw [hon] at h; cases C <;> simp_all [AuthC.isOn, acReceiptOk]) Hms Hai1 Hok
    (by rw [hon]; exact hEok) hdv hwin hF2
  try simp only [srvRunH_applyEntries_specW] at hAE1
  rw [hon] at hAE1
  wp_apply hAE1
    $$ [Hai Hat Hcs Hcv Hst Hbe Happ Hlr Hgr HKV Hao Hfs Hka HRS Hdv Hrun HAR HtokR]
    as ⟨Hfs, Hdv, Hrun, HAR, %st', %ai', %at', %a', %t', %cs', Hai, Hat, Hcs, #Hcv', Hst, HtokR, Hbe, Happ, Hlr, Hgr, Hao, #HWA',
      ⟨%x', %sa', HKV, %Hx', #Hlog', Hka, HRS⟩, %Hpost⟩
  · iframe #; iframe
  iunfold srvFS at Hfs
  icases Hfs with ⟨%sf1, Hsf1⟩
  obtain ⟨hok', hai', hlen', hci', hat'⟩ := Hpost
  have hciL : uint.Z ai ≤ uint.Z (ciEff γ st.k) → uint.Z ai' ≤ uint.Z (ciEff γ st'.k) := by
    intro h
    rcases hci' with ⟨hun, hc⟩ | hc
    · rw [hun, List.length_nil] at hlen'; rw [hc]; omega
    · rw [hc]; omega
  have Hai' : uint.Z ai ≤ uint.Z ai' := by rw [hai']; exact Int.le_max_left _ _
  -- (D22 J1b) the snapshot resources at the new applied index
  ihave Hso := srvSnapOwn_mono s ci E γr _ ai ai' Hai' $$ Hso
  ihave Hss : srvSnapState s ep mst γs ai' (W64 0) $$ [Hsd0 Hsm0 Hsf1]
  · iunfold srvSnapState; iexists _, _, _; iframe Hsd0 Hsm0 Hsf1 Hmst Hslb0
    ipureintro; exact ⟨by have := Hdm0.1; omega, by have := Hdm0.2; omega⟩
  (try wp_auto)
  -- `backend.VerifyBackendConsistency(s.Backend(), s.Logger(), true, schema.AllBuckets...)`
  wp_apply hBk s E.γbe $$ [Hbr] as %be ⟨Hbr, -⟩
  · iframe #; iframe Hbr
  wp_apply hLg s sv.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hV be sv.lg true bsl
  (try wp_auto)
  -- `proposalsApplied.Set(float64(ep.appliedi))`
  iunfold gaugeSetSpec at Hgs
  wp_apply Hgs
  (try wp_auto)
  -- `s.applyWait.Trigger(ep.appliedi)`: the waiters through `ai'`
  icases srvAppliedOwn_lb γr (winGhost ai' (winRest W (unapplied ai ms))) $$ Hao with ⟨Hao, #Hlb⟩
  -- (R2d) the ghost index at least Go's (no overflow: the ghost log's indices are w64s)
  have hnr := winNew_rest_len W (unapplied ai ms)
  have hGlt := idxOk_len_lt _ _ hidxG
  have hGZ : uint.Z (winGhost ai' (winRest W (unapplied ai ms))) =
      uint.Z ai' + (winRest W (unapplied ai ms)).length :=
    winGhost_Z _ _ (by
      rw [List.length_append] at hGlt; have := hlen'; have := hAlen; have := uint_nat_eq ai; omega)
  ihave #Hlb0 := Hlb
  iunfold appliedAtLeast at Hlb0
  ihave #HlbGo : appliedAtLeast γr ai' $$ []
  · iunfold appliedAtLeast
    iapply (monoNatLbOwn_le (uint.nat ai')
      (by have := uint_nat_eq ai'; have := uint_nat_eq (winGhost ai' (winRest W (unapplied ai ms))); omega)) $$ Hlb0
  iunfold isWaitTime at Hwt
  icases Hwt with ⟨%wi, %Hwi, -, #HTrig⟩
  subst Hwi
  wp_apply HTrig $$ []
  · iintro !>; iexact HlbGo
  (try wp_auto)
  -- `<-apply.notifyc`: (D43 M3) the view after the batch deposited
  wp_apply wp_notify_receive γnc nc _ $$ [Hnrc Hdv]
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
      iexists γ, TM, E, b, st', ai', at', a', t', cs'
      iframe HsrvC Hlnil
      isplitr
      · ipureintro; exact beSucc_refl γ E
      iframe Hai Hat Hcs Hcv' Hss Hst HtokR Hbe Happ Hlr Hgr Hbr HAR Hrun
      isplitl [Hao]
      · iexact Hao
      isplitr
      · iexact Hlb
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
      ipureintro; exact ⟨hok', hai', hci'.imp_left And.right, hciL, hat'⟩
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
  -- (R2d, Q16 (2)) Go's applied log: the ghost log's first `ai` entries and the batch
  have hlenA : uint.nat ai' = (A.take (uint.nat ai) ++ unapplied ai ms).length := by
    rw [List.length_append, List.length_take, Nat.min_eq_left (by omega)]
    have := hlen'; have := uint_nat_eq ai; have := uint_nat_eq ai'; omega
  have hltA : lastTermIs (A.take (uint.nat ai) ++ unapplied ai ms) at' := lastTermIs_append hAT hat'
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
  ihave #HlbGo := srvRLogLb_mono γr.raft _ _ hGoPre $$ HlbB
  ihave Hstor : srvSnapStor mst γs γr nk ai' at' $$ []
  · iunfold srvSnapStor
    iframe Hmsi
    isplitr
    · rw [← hidx, ← hρr]; iexact Hsdl
    isplitr
    · rw [← hρr]; iexact Hrli
    iexists A.take (uint.nat ai) ++ unapplied ai ms
    iframe HlbGo
    ipureintro; exact ⟨by rw [← hlenA]; try word, hltA⟩
  ihave ⟨#Hfz, #Hft⟩ := srv_frozen_of_terms γs (A.take (uint.nat ai) ++ unapplied ai ms) ai' at' hlenA hltA $$ Hfts
  ihave #Hecs : iprop(⌜uint.Z ai' = 0⌝ ∨ epCsCfg γr cs') $$ []
  · by_cases hL : A ++ winNew W (unapplied ai ms) = []
    · ileft; ipureintro
      have h0 := hGoPre.length_le
      rw [hL, List.length_nil] at h0
      have h0' : uint.nat ai' = 0 := by omega
      word
    · iright; iunfold epCsCfg; rw [← hρr]
      iapply epCsAt_ne _ _ _ hL $$ Hcv'
  -- `s.snapshotIfNeededAndCompactRaftLog(ep)`
  have hS1 := hSINC.1 s E ρ.wait γ ci b γr ep st' ai' at' cs' a' t' x' mst γs nk γp
    (w + (unapplied ai ms).length) TM ρ sa' q γn
  rw [hon] at hS1
  wp_apply hS1 hok'
      (hciL hciA0) Hdisk.2.1.2.2.1 hsz Hdisk.2.2.1 hγn hpre
    $$ [Hss Hai Hat Hcs Hst Hbe Happ Hlr HKV HwalT Hstor]
    as ⟨%st'', Hss, -, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, HwalT, %Hst''⟩
  · iframe #; iframe
  (try wp_auto)
  ihave HKV := (srvApplyKVM_C C s E ρ.wait x' sa').1 $$ HKV
  iunfold epConfState at Hcs
  icases Hcs with ⟨Hcs, #Hcsok⟩
  -- (2026-10-31, S1) the step's end, shared by the select's branches: the apply thread at a state
  -- `stF` of the same consistent index
  ihave Hfin : iprop(∀ stF : ApplyState, ⌜loopOk γ stF ai' ∧ ciEff γ stF.k = ciEff γ st'.k⌝ -∗
      epAppliedIAddr ep ↦ ai' -∗ epAppliedTAddr ep ↦ at' -∗ epConfStateAddr ep ↦ cs' -∗
      applyThread γ stF -∗ applyBackend γ ci b -∗ ciApplying ci a' t' -∗ srvLgReader s -∗
      srvGoRes s -∗ srvApplyKVC C s E ρ.wait x' sa' -∗
      kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 (A ++ winNew W (unapplied ai ms)) x' sa' -∗
      srvRestW E γr (A ++ winNew W (unapplied ai ms)) (winDone D W (unapplied ai ms)) -∗ Φ #()) $$ [HΦ Hss Hbr HAR Hrun Hao HwalT HtokR Hso]
  · iintro %stF %HF Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka HRS
    ihave Hcs : epConfState ep cs' $$ [Hcs]
    · iunfold epConfState; iframe Hcs Hcsok
    ihave HtokR : acTok C (ciEff γ stF.k) $$ [HtokR]
    · rw [HF.2, ← srvTokRights_eq C E _ hM]; iexact HtokR
    iapply HΦ
    iexists γ, TM, E, b, stF, ai', at', a', t', cs'
    iframe HsrvC Hlnil
    isplitr
    · ipureintro; exact beSucc_refl γ E
    iframe Hai Hat Hcs Hcv' Hss Hst HtokR Hbe Happ Hlr Hgr Hbr HAR Hrun
    isplitl [Hao]
    · iexact Hao
    isplitr
    · iexact Hlb
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
    exact ⟨HF.1, hai', by rw [HF.2]; exact hci'.imp_left And.right, by rw [HF.2]; exact hciL, hat'⟩
  -- `select { case m := <-s.r.msgSnapC: ...; default: }` (2026-10-31, S1: a `MsgSnap` raft handed
  -- out, merged with the backend's image and sent when the guard holds)
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
        icases HP with ⟨%sm, Hm, %Hty, #Hsm, -⟩
        rw [Hγm]
        letI := srvStor (GF := GF) γr.raft.raft
        ihave %Hsh := sentMsg_shape _ _ _ _ $$ Hsm
        obtain ⟨sn, hsn, -⟩ := Hsh.2 Hty
        ihave %Hsnp := srv_sentSnap_pos γr γm.id sm sn Hty hsn $$ [Hrli' Hsm]
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
            have HifI := Hif
            -- (R2d) in a window still pending after the batch the merged image would be at Go's
            -- index below the ghost one (the Q16-3 review's finding 1): no merged send then
            -- (`winNoMergedSend`, an assumption R2s discharges)
            by_cases hR : winRest W (unapplied ai ms) = []
            rotate_left
            · iunfold winNoMergedSend at Hnms
              icases Hnms with (%hW0 | #Hnms)
              · exfalso; apply hR; rw [hW0]; rfl
              · ihave %hns := Hnms $$ Hsm
                exact absurd Hty hns
            -- the window over: the ghost log is Go's applied log
            have hnl := winRest_nil_len W (unapplied ai ms) hR
            have hGlen : (A ++ winNew W (unapplied ai ms)).length = uint.nat ai' := by
              rw [List.length_append]; have := hlen'; have := uint_nat_eq ai; have := uint_nat_eq ai'
              omega
            have hGgo : A.take (uint.nat ai) ++ unapplied ai ms = A ++ winNew W (unapplied ai ms) :=
              hGoPre.eq_of_length (by rw [← hlenA, hGlen])
            have hltG : lastTermIs (A ++ winNew W (unapplied ai ms)) at' := hGgo ▸ hltA
            have hdn : winDone D W (unapplied ai ms) = [] := by unfold winDone; rw [hR]
            have hRSeq : srvRestW E γr (A ++ winNew W (unapplied ai ms)) (winDone D W (unapplied ai ms)) =
                srvRest E γr (A ++ winNew W (unapplied ai ms)) := by rw [hdn, srvRestW_nil]
            have hGh : winGhost ai' (winRest W (unapplied ai ms)) = ai' := by rw [hR]; rfl
            ihave #Hlog'' : appliedLogAt γr ai' x'.log $$ []
            · have e : appliedLogAt (GF := GF) γr (winGhost ai' (winRest W (unapplied ai ms))) x'.log =
                  appliedLogAt γr ai' x'.log := by rw [hGh]
              rw [← e]; iexact Hlog'
            ihave HRS : srvRest E γr (A ++ winNew W (unapplied ai ms)) $$ [HRS]
            · rw [← srvRestW_nil, ← hdn]; iexact HRS
            have hciE : ciEff γ st''.k = ai' := by
              rw [Hst''.2]
              have h1 := hciL hciA0
              have hcw : uint.Z (ciEff γ st.k) ≤ uint.Z ai' := by
                have := hcia; have := hAL; have := hlen'; have := uint_nat_eq ai; omega
              have h2 : uint.Z (ciEff γ st'.k) ≤ uint.Z ai' := by
                rcases hci' with ⟨-, hc⟩ | hc
                · rw [hc]; exact hcw
                · rw [hc]; omega
              word
            have hlenZ : uint.Z ai' = ((A ++ winNew W (unapplied ai ms)).length : Int) := by
              have := hGlen; have := uint_nat_eq ai'; omega
            have hpos : 0 < uint.Z ai' := by word
            (try wp_auto)
            -- (S2's `mergedCreate_window`) the commit's and the snapshot's contracts
            icases srvApplyKVC_coreA C s E ρ.wait x' sa' $$ HKV with ⟨%ua, HKVc, HAr, HKVk⟩
            -- the component lends its buckets to the window (none off)
            ihave HL := acRes_lend C s E ua sa' hM $$ HAr
            icases Hkv with ⟨%kv, #Hkvf, #Hkvi⟩
            imod mergedCreate_window hC hSnap hOn hSave hPut hUR hID hName hSafe C.isOn s γ ci TM E ρ
                γr b st'' ai' a' t' (A ++ winNew W (unapplied ai ms)) x' ρ.wait γp ua kv Hst''.1 hciE hpos hlenZ
                (acBkts C) (acImg C sa') (acRes C s E ua sa') (acBkts_rest C)
              $$ [Hst Hbe Happ HKVc HRS Hr1 Hl1 Hr2 Hl2 HL]
              with ⟨%be, %dq, %RC, %RC', %RS, %RS', Hkc, HRC, Hbeo, Hbs, HRCS, Hback⟩
            · iframe Hpkg Hsrv Hkvf Hkvi HW Hlog'' HlbB Hr1 Hl1 Hr2 Hl2 Hst Hbe Happ HKVc HRS HL
            wp_apply (hCM s m sm at' ai' cs' sv.lg kv be dq RC RC' RS RS' _)
              $$ [Hlr Hkc HRC Hbeo Hbs HRCS Hm]
              as %mg ⟨Hlr, HRS', Hbeo, %rc, %D, %c, #Hmg, #Hml, #Hcso, Hrs, %HQd⟩
            · iframe #; iframe Hlr Hkc HRC Hbeo Hbs HRCS Hm; ipureintro; exact Hlgnn
            imod Hback $$ HRS' Hbeo with ⟨%st3, Hst, Hbe, Happ, HKVc, HRS, HAr, %Hst3⟩
            ihave HKV := HKVk $$ HKVc HAr
            icases srvApplyKVC_idxCert C s E ρ.wait x' sa' $$ HKV with ⟨HKV, #Hicx⟩
            ihave #Hrcx := mvcc.idxCert_rcpt E.γ.idx x'.log $$ Hicx
            -- the merged message sent: of a term committed through the applied index (the batch's
            -- term, `rnRtOk`; not `0`, a `MsgSnap`'s term), certified at the voters' conf state
            iunfold rnRtOk at Hrt
            rw [hγn]
            icases Hrt with (%Hrt0 | ⟨%ct, #Hct, %Hnct⟩)
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
            imod srv_merged_sent γr (A ++ winNew W (unapplied ai ms)) ai' at' c γm.id ct sm sn hpos h61 hsz hlenZ
                hltG Hcs0 Hty hsn (by word)
                (by have hn' := hnA; rw [hGgo] at hn'; have := hGlen; have := uint_nat_eq ai'; omega)
              $$ [Hrli' HlbB Hsm Hct] with #Hsm'
            · iframe Hrli' HlbB Hsm Hct
            -- (`merged_imageC`) the image's certificate: the component's buckets the lent part's
            ihave Hmi : |={⊤}=> kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 (A ++ winNew W (unapplied ai ms)) x' sa' ∗
                □ (srvNet (GF := GF) γr.raft.raft).img ai' D $$ [Hka]
            · iapply (merged_imageC C s γ ci TM E ρ γr ai' (A ++ winNew W (unapplied ai ms)) x' sa' D hM hlenZ
                Hkv0)
              iframe Hsrv Hka Hrcx; ipureintro; exact HQd
            imod Hmi with ⟨Hka, #Himg⟩
            imod srvMerged_bundle γr.raft.raft m rc sm γm.id c ai' at' D Hty
              $$ [Hml Hsm' Hrs Himg] with Hbun
            · iframe Hml Hsm' Hrs Himg
            (try wp_auto)
            wp_apply (hSMS s mg m rc sv.lg sv.memberID stg tr γN SN TSN lid) $$ [Hgr Hlr Hbun]
              as ⟨Hgr, Hlr⟩
            · iframe #; iframe Hgr Hlr; rw [HγN]; iframe Hbun; ipureintro; exact Hlgnn
            (try wp_auto)
            have hF3 : loopOk γ st3 ai' ∧ ciEff γ st3.k = ciEff γ st'.k :=
              ⟨Hst3.1, by rw [Hst3.2]; exact Hst''.2⟩
            iapply Hfin $$ %st3 %hF3 Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka
            rw [hRSeq]; iexact HRS
          · (try wp_auto)
            iapply Hfin $$ %st'' %Hst'' Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka HRS
        · (try wp_auto)
          iapply Hfin $$ %st'' %Hst'' Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka HRS
      · itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- `default`
    (try wp_auto)
    iapply Hfin $$ %st'' %Hst'' Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka HRS

set_option maxRecDepth 100000 in
/-- **`applyAll.spec`** (the auth component's stage 2, 2026-11-04: in both auth modes): the batch
(`wp_proofBatch`) and the snapshot payload in the server's mode (`wp_proofSnapM`, from the off
case `wp_proofSnap`). -/
theorem EtcdServer.applyAll.wp_proof
    (hASnap : EtcdServer.applySnapshot.spec (GF := GF) (hG := hG))
    (hAE : EtcdServer.applyEntries.spec (GF := GF) (hG := hG))
    (hBk : EtcdServer.Backend.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hV : backend.VerifyBackendConsistency.spec (GF := GF) (hG := hG))
    (hSINC : EtcdServer.snapshotIfNeededAndCompactRaftLog.spec (GF := GF) (hG := hG))
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
    EtcdServer.applyAll.spec (GF := GF) (hG := hG) :=
  ⟨EtcdServer.applyAll.wp_proofBatch hASnap hAE hBk hLg hV hSINC hGT hGS hGM hGI hCM hSMS hC hSnap hOn hSave
      hPut hUR hID hName hSafe,
    EtcdServer.applyAll.wp_proofSnapM
      (EtcdServer.applyAll.wp_proofSnap hASnap.2 hAE.2 hBk hLg hV hSINC.2 hGT hGS hGM hGI hCM hSMS hC
        hSnap hOn hSave hPut hUR hID hName hSafe)
      hASnap.2 hAE.2 hBk hLg hV hSINC.2 hGT hGS hGM hGI hCM hSMS hC hSnap hOn hSave hPut hUR hID hName
      hSafe⟩

end proof

end EtcdGrove
end Perennial
