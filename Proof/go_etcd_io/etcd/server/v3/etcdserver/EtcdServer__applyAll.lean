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
theorem EtcdServer.applyAll.wp_proofBatch
    (hASnap : EtcdServer.applySnapshot.specEmpty (GF := GF) (hG := hG))
    (hAE : EtcdServer.applyEntries.specBatch (GF := GF) (hG := hG))
    (hBk : EtcdServer.Backend.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hV : backend.VerifyBackendConsistency.spec (GF := GF) (hG := hG))
    (hSINC : EtcdServer.snapshotIfNeededAndCompactRaftLog.specBatch (GF := GF) (hG := hG))
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
  intro s γ ci TM E ρ γr b ep ap es ents ms f0 rac nc st ai at0 a t cs x A mst γs γp dv γnc w nk q γn rt n Hms Hai1
    Hok hEok hdv hAL hAT Hdisk hciA hcia hγn hnA
  simp only [srvRunH_applyAll_spec]
  have hAE := EtcdServer.applyEntries.spec_off hAE
  unfold EtcdServer.applyEntries.specOff at hAE
  wp_start as ⟨#Hsrv, #Hsa, #Hbw, #Hes, #Hrac, #Hracc, #Hsn, #Hnc, #Hncb, Hnrc, #Hesl, #Hentsat, Hai, Hat, Hcs, #Hcv,
    Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, HKV, Hao, #Hlog, #Hbc, #HW, #HWA, Hka, HRS, #Hkb, Hdv, #Hdvr, HAR, Hrun, #Hsd, #Hkv, #Hmsi, HwalT, #Hrtf, #Hrt, Hso⟩
  icases srvApRes_cfg_size s γr A $$ HAR with ⟨HAR, %hsz⟩
  ihave #Hsrv' := Hsrv
  iunfold isServer at Hsrv'
  icases Hsrv' with ⟨%Hρrd, -, ⟨%sv, #Hfl⟩, -, -, #HrnS, -⟩
  iunfold srvFieldsAt at Hfl
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
  wp_apply hASnap s ep ap $$ []
  · iframe #
  (try wp_auto)
  -- `s.applyEntries(ep, apply)`, lending it `forceDiskSnapshot` (D14i)
  iunfold srvSnapState at Hss
  icases Hss with ⟨%sd0, %sm0, %sf0, Hsd0, Hsm0, Hsf0, %Hdm0, #Hmst, #Hslb0⟩
  ihave Hfs : srvFS s $$ [Hsf0]
  · iunfold srvFS; iexists _; iexact Hsf0
  wp_apply hAE s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr A γp dv w Hms Hai1 Hok
    hEok hdv
    $$ [Hai Hat Hcs Hcv Hst Hbe Happ Hlr Hgr HKV Hao Hfs Hka HRS Hdv Hrun HAR]
    as ⟨Hfs, Hdv, Hrun, HAR, %st', %ai', %at', %a', %t', %cs', Hai, Hat, Hcs, #Hcv', Hst, Hbe, Happ, Hlr, Hgr, Hao, #HWA',
      ⟨%x', HKV, %Hx', #Hlog', Hka, HRS⟩, %Hpost⟩
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
  ihave Hso := srvSnapOwn_mono s ci E γr ai ai' Hai' $$ Hso
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
      iapply HΦ
      iexists γ, TM, E, b, st', ai', at', a', t', cs'
      iframe Hsrv
      isplitr
      · ipureintro; exact beSucc_refl γ E
      iframe Hai Hat Hcs Hcv' Hss Hst Hbe Happ Hlr Hgr Hbr HAR Hrun
      isplitl [Hao]
      · iexact Hao
      isplitr
      · iexact Hlb
      isplitr
      · iexact HWA'
      isplitl [HKV Hka HRS]
      · iexists x'; iframe HKV Hlog' Hka HRS; ipureintro; exact Hx'
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
  icases Hadv with ⟨#Hnal, #Hsdl, -, #Hfts⟩
  ihave #Hnal' : (letI := srvStor (GF := GF) γr.raft.raft; nodeAppliedLb γr.raft.raft.cl nk (uint.nat ai')) $$ []
  · rw [← hidx, ← hρr]; iexact Hnal
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
  imod authOn_false_of_off s γ ci TM E ρ γr ρ.wait x' _ $$ [$Hsrv $HKV $Hka] with ⟨%Hoff, HKV, Hka⟩
  ihave #HsrvM : isServerM false s γ ci TM E ρ γr $$ []
  · rw [isServerM_false]; iexact Hsrv
  wp_apply EtcdServer.snapshotIfNeededAndCompactRaftLog.spec_off hSINC s E ρ.wait γ ci b γr ep st'
      ai' at' cs' a' t' x' mst γs nk γp (w + (unapplied ai ms).length) TM ρ q Hoff hok'
      (hciL hciA) Hdisk.2.1.2.2.1 hsz Hdisk.2.2.1
    $$ [Hss Hai Hat Hcs Hst Hbe Happ Hlr HKV HwalT Hstor]
    as ⟨%st'', Hss, -, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, HwalT, %Hst''⟩
  · iframe #; iframe
  (try wp_auto)
  iunfold epConfState at Hcs
  icases Hcs with ⟨Hcs, #Hcsok⟩
  -- (2026-10-31, S1) the step's end, shared by the select's branches: the apply thread at a state
  -- `stF` of the same consistent index
  ihave Hfin : iprop(∀ stF : ApplyState, ⌜loopOk γ stF ai' ∧ ciEff γ stF.k = ciEff γ st'.k⌝ -∗
      epAppliedIAddr ep ↦ ai' -∗ epAppliedTAddr ep ↦ at' -∗ epConfStateAddr ep ↦ cs' -∗
      applyThread γ stF -∗ applyBackend γ ci b -∗ ciApplying ci a' t' -∗ srvLgReader s -∗
      srvGoRes s -∗ srvApplyKV s E ρ.wait x' -∗ kvApplied γr.raft γr.kv (A ++ unapplied ai ms) x' -∗
      srvRest E γr (A ++ unapplied ai ms) -∗ Φ #()) $$ [HΦ Hss Hbr HAR Hrun Hao HwalT Hso]
  · iintro %stF %HF Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka HRS
    ihave Hcs : epConfState ep cs' $$ [Hcs]
    · iunfold epConfState; iframe Hcs Hcsok
    iapply HΦ
    iexists γ, TM, E, b, stF, ai', at', a', t', cs'
    iframe Hsrv
    isplitr
    · ipureintro; exact beSucc_refl γ E
    iframe Hai Hat Hcs Hcv' Hss Hst Hbe Happ Hlr Hgr Hbr HAR Hrun
    isplitl [Hao]
    · iexact Hao
    isplitr
    · iexact Hlb
    isplitr
    · iexact HWA'
    isplitl [HKV Hka HRS]
    · iexists x'; iframe HKV Hlog' Hka HRS; ipureintro; exact Hx'
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
            icases srvApplyKV_core s E ρ.wait x' $$ HKV with ⟨%ua, HKVc, HKVk⟩
            icases Hkv with ⟨%kv, #Hkvf, #Hkvi⟩
            imod mergedCreate_window hC hSnap hOn hSave hPut hUR hID hName hSafe false s γ ci TM E ρ
                γr b st'' ai' a' t' (A ++ unapplied ai ms) x' ρ.wait γp ua kv Hst''.1 hciE hpos hlenZ
              $$ [Hst Hbe Happ HKVc HRS Hr1 Hr2]
              with ⟨%be, %dq, %RC, %RC', %RS, %RS', Hkc, HRC, Hbeo, Hbs, HRCS, Hback⟩
            · iframe Hpkg HsrvM Hkvf Hkvi HW Hlog' HlbB Hr1 Hr2 Hst Hbe Happ HKVc HRS
            wp_apply (hCM s m sm at' ai' cs' sv.lg kv be dq RC RC' RS RS'
                (mergedObs γr E.cmp ai' (A ++ unapplied ai ms) x'.log))
              $$ [Hlr Hkc HRC Hbeo Hbs HRCS Hm]
              as %mg ⟨Hlr, HRS', Hbeo, %rc, %D, %c, #Hmg, #Hml, #Hcso, Hrs, %HQd⟩
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
            -- (S2's `merged_image`) the image's certificate
            imod merged_image s γ ci TM E ρ γr ai' (A ++ unapplied ai ms) x' D hlenZ Hkv0
              $$ [Hka] with ⟨Hka, #Himg⟩
            · iframe Hsrv Hka; ipureintro; exact HQd
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


/-- **`applyAll.specOn`** (the auth plan's E3p): `wp_proof` over the callees' mode-`on` specs. -/
theorem EtcdServer.applyAll.wp_proofOn
    (hASnap : EtcdServer.applySnapshot.specEmpty (GF := GF) (hG := hG))
    (hAE : EtcdServer.applyEntries.specOn (GF := GF) (hG := hG))
    (hBk : EtcdServer.Backend.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hV : backend.VerifyBackendConsistency.spec (GF := GF) (hG := hG))
    (hSINC : EtcdServer.snapshotIfNeededAndCompactRaftLog.specBatch (GF := GF) (hG := hG))
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
    EtcdServer.applyAll.specOn (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr b ep ap es ents ms f0 rac nc st ai at0 a t cs x A mst γs γp dv γnc w nk γa sa q γn rt n hM hRB
    Hms Hai1 Hok hEok hdv hAL hAT Hdisk hciA hcia hγn hnA
  simp only [srvRunH_applyAll_spec]
  unfold EtcdServer.applyEntries.specOn at hAE
  wp_start as ⟨#Hsrv, #Hlnil, #Hsa, #Hbw, #Hes, #Hrac, #Hracc, #Hsn, #Hnc, #Hncb, Hnrc, #Hesl, #Hentsat, Hai, Hat, Hcs, #Hcv,
    Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, HKV, Hao, #Hlog, #Hbc, #HW, #HWA, Hka, HRS, #Hkb, Hdv, #Hdvr, HAR, Hrun, HtokR, #Hsd, #Hkv, #Hmsi, HwalT, #Hrtf, #Hrt, Hso⟩
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
  wp_apply hASnap s ep ap $$ []
  · iframe #
  (try wp_auto)
  -- `s.applyEntries(ep, apply)`, lending it `forceDiskSnapshot` (D14i)
  iunfold srvSnapState at Hss
  icases Hss with ⟨%sd0, %sm0, %sf0, Hsd0, Hsm0, Hsf0, %Hdm0, #Hmst, #Hslb0⟩
  ihave Hfs : srvFS s $$ [Hsf0]
  · iunfold srvFS; iexists _; iexact Hsf0
  wp_apply hAE s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr A γp dv w γa sa hM hRB
    Hms Hai1 Hok hEok hdv
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
  ihave Hso := srvSnapOwn_mono s ci E γr ai ai' Hai' $$ Hso
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
      iapply HΦ
      iexists γ, TM, E, b, st', ai', at', a', t', cs'
      iframe Hsrv
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
  icases Hadv with ⟨#Hnal, #Hsdl, -, #Hfts⟩
  ihave #Hnal' : (letI := srvStor (GF := GF) γr.raft.raft; nodeAppliedLb γr.raft.raft.cl nk (uint.nat ai')) $$ []
  · rw [← hidx, ← hρr]; iexact Hnal
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
  wp_apply EtcdServer.snapshotIfNeededAndCompactRaftLog.spec_on hSINC s E ρ.wait γ ci b γr ep st'
      ai' at' cs' a' t' x' mst γs nk γp (w + (unapplied ai ms).length) TM ρ sa' q
      (by rw [apply.AEnv.authOn_eq, hM]; rfl) hok'
      (hciL hciA) Hdisk.2.1.2.2.1 hsz Hdisk.2.2.1
    $$ [Hss Hai Hat Hcs Hst Hbe Happ Hlr HKV HwalT Hstor]
    as ⟨%st'', Hss, -, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, HwalT, %Hst''⟩
  · iframe #; iframe
  (try wp_auto)
  iunfold epConfState at Hcs
  icases Hcs with ⟨Hcs, #Hcsok⟩
  -- (2026-10-31, S1) the step's end, shared by the select's branches: the apply thread at a state
  -- `stF` of the same consistent index
  ihave Hfin : iprop(∀ stF : ApplyState, ⌜loopOk γ stF ai' ∧ ciEff γ stF.k = ciEff γ st'.k⌝ -∗
      epAppliedIAddr ep ↦ ai' -∗ epAppliedTAddr ep ↦ at' -∗ epConfStateAddr ep ↦ cs' -∗
      applyThread γ stF -∗ applyBackend γ ci b -∗ ciApplying ci a' t' -∗ srvLgReader s -∗
      srvGoRes s -∗ srvApplyKVOn s E ρ.wait x' sa' -∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 (A ++ unapplied ai ms) x' sa' -∗
      srvRest E γr (A ++ unapplied ai ms) -∗ Φ #()) $$ [HΦ Hss Hbr HAR Hrun Hao HwalT HtokR Hso]
  · iintro %stF %HF Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka HRS
    ihave Hcs : epConfState ep cs' $$ [Hcs]
    · iunfold epConfState; iframe Hcs Hcsok
    ihave HtokR : srvTokRights E (ciEff γ stF.k) $$ [HtokR]
    · rw [HF.2]; iexact HtokR
    iapply HΦ
    iexists γ, TM, E, b, stF, ai', at', a', t', cs'
    iframe Hsrv
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
            icases srvApplyKVOn_core s E ρ.wait x' sa' $$ HKV with ⟨%ua, HKVc, HKVk⟩
            icases Hkv with ⟨%kv, #Hkvf, #Hkvi⟩
            imod mergedCreate_window hC hSnap hOn hSave hPut hUR hID hName hSafe true s γ ci TM E ρ
                γr b st'' ai' a' t' (A ++ unapplied ai ms) x' ρ.wait γp ua kv Hst''.1 hciE hpos hlenZ
              $$ [Hst Hbe Happ HKVc HRS Hr1 Hr2]
              with ⟨%be, %dq, %RC, %RC', %RS, %RS', Hkc, HRC, Hbeo, Hbs, HRCS, Hback⟩
            · iframe Hpkg Hsrv Hkvf Hkvi HW Hlog' HlbB Hr1 Hr2 Hst Hbe Happ HKVc HRS
            wp_apply (hCM s m sm at' ai' cs' sv.lg kv be dq RC RC' RS RS'
                (mergedObs γr E.cmp ai' (A ++ unapplied ai ms) x'.log))
              $$ [Hlr Hkc HRC Hbeo Hbs HRCS Hm]
              as %mg ⟨Hlr, HRS', Hbeo, %rc, %D, %c, #Hmg, #Hml, #Hcso, Hrs, %HQd⟩
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
            -- (S2's `merged_image`) the image's certificate
            -- with auth on, the KV log is the mode-on model's, not the image `srvNet` carries
            -- (`merged_image` is of the mode off): open (`notes/decisions.md`, "applyAll's merge
            -- branch (S1)")
            ihave #Himg : □ (srvNet (GF := GF) γr.raft.raft).img ai' D $$ []
            · sorry -- SNAPSHOT-SORRY #7-on: the merged snapshot's image with auth on
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

set_option maxRecDepth 100000 in
/-- **`applyAll.spec`** (J8b, 2026-11-01): `wp_proofBatch` and `wp_proofSnap` (`ApplyAllSnap.lean`). -/
theorem EtcdServer.applyAll.wp_proof
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
    EtcdServer.applyAll.spec (GF := GF) (hG := hG) :=
  ⟨EtcdServer.applyAll.wp_proofBatch hASnap.1 hAE.1 hBk hLg hV hSINC.1 hGT hGS hGM hGI hCM hSMS hC hSnap hOn hSave hPut hUR hID hName hSafe,
    EtcdServer.applyAll.wp_proofSnap hASnap.2 hAE.2 hBk hLg hV hSINC.2 hGT hGS hGM hGI hCM hSMS hC hSnap hOn hSave hPut hUR hID hName hSafe⟩

end proof

end EtcdGrove
end Perennial
