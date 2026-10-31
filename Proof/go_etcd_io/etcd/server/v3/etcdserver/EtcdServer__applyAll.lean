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
theorem EtcdServer.applyAll.wp_proof
    (hASnap : EtcdServer.applySnapshot.spec (GF := GF) (hG := hG))
    (hAE : EtcdServer.applyEntries.spec (GF := GF) (hG := hG))
    (hBk : EtcdServer.Backend.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hV : backend.VerifyBackendConsistency.spec (GF := GF) (hG := hG))
    (hSINC : EtcdServer.snapshotIfNeededAndCompactRaftLog.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyAll.spec (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr b ep ap es ents ms f0 rac nc st ai at0 a t cs x A mst γs γp dv γnc w nid q Hms Hai1
    Hok hEok hdv haw hAL hAT Hdisk hciA
  simp only [srvRunH_applyAll_spec]
  have hAE := EtcdServer.applyEntries.spec_off hAE
  unfold EtcdServer.applyEntries.specOff at hAE
  wp_start as ⟨#Hsrv, #Hsa, #Hbw, #Hes, #Hrac, #Hracc, #Hsn, #Hnc, #Hncb, Hnrc, #Hesl, #Hentsat, Hai, Hat, Hcs, #Hcv,
    Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, HKV, Hao, #Hlog, #Hbc, #HW, #HWA, Hka, HRS, #Hkb, Hdv, #Hdvr, HAR, Hrun, #Hsd, #Hkv, #Hmsi, HwalT⟩
  icases srvApRes_cfg_size s γr A $$ HAR with ⟨HAR, %hsz⟩
  ihave #Hsrv' := Hsrv
  iunfold isServer at Hsrv'
  icases Hsrv' with ⟨%Hρrd, -, ⟨%sv, #Hfl⟩, -, -, #HrnS⟩
  iunfold srvFieldsAt at Hfl
  icases Hfl with ⟨#Hlgf, %Hlgnn, -⟩
  ihave #Hsa' := Hsa
  iunfold isServerApplyAll at Hsa'
  icases Hsa' with ⟨%wt, %msc, %sc, #Hwtf, #Hwt, #Hmscf, ⟨%γc, %Pm, #Hmscb⟩, #Hsc,
    ⟨%stg, #Hstgf, #Hstgc⟩, -, -, -⟩
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
  ihave #Hnal' : (letI := srvStor (GF := GF) γr.raft.raft; nodeAppliedLb γr.raft.raft.cl nid (uint.nat ai')) $$ []
  · rw [← hidx, ← hρr]; iexact Hnal
  ihave #HrnS' := HrnS
  iunfold srvRaftNode at HrnS'
  icases HrnS' with ⟨%rn0, -, HrpS⟩
  iunfold raftPropose at HrpS
  icases HrpS with ⟨%rni0, -, #Hrli, -⟩
  ihave #Hkb' := Hkb
  iunfold kvBatch at Hkb'
  icases Hkb' with ⟨#HlbB, -⟩
  ihave Hstor : srvSnapStor mst γs γr nid ai' at' $$ []
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
      ai' at' cs' a' t' x' mst γs nid γp (w + (unapplied ai ms).length) TM ρ q Hoff hok'
      (by have := hlen'; push_cast; omega) (hciL hciA) Hdisk.2.1.2.2.1 hsz Hdisk.2.2.1
    $$ [Hss Hai Hat Hcs Hst Hbe Happ Hlr HKV HwalT Hstor]
    as ⟨%st'', Hss, -, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, HwalT, %Hst''⟩
  · iframe #; iframe
  (try wp_auto)
  iunfold epConfState at Hcs
  icases Hcs with ⟨Hcs, #Hcsok⟩
  -- `select { case m := <-s.r.msgSnapC: ...; default: }`
  ihave #Hmscch := is_bag_is_chan γc msc Pm $$ Hmscb
  rw [isChanBag_unseal] at *
  iunfold isChanBagDef at Hmscb
  icases Hmscb with ⟨-, #Hinv⟩
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
      unfold nonblockingRecvAu nonblockingRecvAuInner
      isplit
      · iinv Hinv with Hi Hclose
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hmask
        inext
        unfold chanBagInv
        icases Hi with ⟨%st0, Hoc, Hi⟩
        iexists st0
        iframe Hoc
        rcases st0 with (_ | ⟨v, rest⟩) | _ | v | _ | _ | _ | (_ | ⟨_, _⟩)
        all_goals dsimp only
        case Buffered.cons | SndPending =>
          sorry -- SNAPSHOT-SORRY #7: the `msgSnapC` merge branch (a `MsgSnap` received: `createMergedSnapshotMessage`/`sendMergedSnap` over `rnSnapMsg`)
        all_goals first | itrivial | (iexfalso; iexact Hi)
      · itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- `default`
    (try wp_auto)
    ihave Hcs : epConfState ep cs' $$ [Hcs]
    · iunfold epConfState; iframe Hcs Hcsok
    iapply HΦ
    iexists γ, TM, E, b, st'', ai', at', a', t', cs'
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
    ipureintro
    exact ⟨Hst''.1, hai', by rw [Hst''.2]; exact hci'.imp_left And.right, by rw [Hst''.2]; exact hciL, hat'⟩


/-- **`applyAll.specOn`** (the auth plan's E3p): `wp_proof` over the callees' mode-`on` specs. -/
theorem EtcdServer.applyAll.wp_proofOn
    (hASnap : EtcdServer.applySnapshot.spec (GF := GF) (hG := hG))
    (hAE : EtcdServer.applyEntries.specOn (GF := GF) (hG := hG))
    (hBk : EtcdServer.Backend.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hV : backend.VerifyBackendConsistency.spec (GF := GF) (hG := hG))
    (hSINC : EtcdServer.snapshotIfNeededAndCompactRaftLog.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyAll.specOn (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr b ep ap es ents ms f0 rac nc st ai at0 a t cs x A mst γs γp dv γnc w nid γa sa q hM hRB
    Hms Hai1 Hok hEok hdv haw hAL hAT Hdisk hciA
  simp only [srvRunH_applyAll_spec]
  unfold EtcdServer.applyEntries.specOn at hAE
  wp_start as ⟨#Hsrv, #Hlnil, #Hsa, #Hbw, #Hes, #Hrac, #Hracc, #Hsn, #Hnc, #Hncb, Hnrc, #Hesl, #Hentsat, Hai, Hat, Hcs, #Hcv,
    Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, HKV, Hao, #Hlog, #Hbc, #HW, #HWA, Hka, HRS, #Hkb, Hdv, #Hdvr, HAR, Hrun, HtokR, #Hsd, #Hkv, #Hmsi, HwalT⟩
  icases srvApRes_cfg_size s γr A $$ HAR with ⟨HAR, %hsz⟩
  ihave #Hsrv' := Hsrv
  iunfold isServerM at Hsrv'
  icases Hsrv' with ⟨%Hρrd, -, ⟨%sv, #Hfl⟩, -, -, #HrnS⟩
  iunfold srvFieldsAtM at Hfl
  icases Hfl with ⟨#Hlgf, %Hlgnn, -⟩
  ihave #Hsa' := Hsa
  iunfold isServerApplyAll at Hsa'
  icases Hsa' with ⟨%wt, %msc, %sc, #Hwtf, #Hwt, #Hmscf, ⟨%γc, %Pm, #Hmscb⟩, #Hsc,
    ⟨%stg, #Hstgf, #Hstgc⟩, -, -, -⟩
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
  ihave #Hnal' : (letI := srvStor (GF := GF) γr.raft.raft; nodeAppliedLb γr.raft.raft.cl nid (uint.nat ai')) $$ []
  · rw [← hidx, ← hρr]; iexact Hnal
  ihave #HrnS' := HrnS
  iunfold srvRaftNode at HrnS'
  icases HrnS' with ⟨%rn0, -, HrpS⟩
  iunfold raftPropose at HrpS
  icases HrpS with ⟨%rni0, -, #Hrli, -⟩
  ihave #Hkb' := Hkb
  iunfold kvBatch at Hkb'
  icases Hkb' with ⟨#HlbB, -⟩
  ihave Hstor : srvSnapStor mst γs γr nid ai' at' $$ []
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
      ai' at' cs' a' t' x' mst γs nid γp (w + (unapplied ai ms).length) TM ρ sa' q
      (by rw [apply.AEnv.authOn_eq, hM]; rfl) hok'
      (by have := hlen'; push_cast; omega) (hciL hciA) Hdisk.2.1.2.2.1 hsz Hdisk.2.2.1
    $$ [Hss Hai Hat Hcs Hst Hbe Happ Hlr HKV HwalT Hstor]
    as ⟨%st'', Hss, -, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, HwalT, %Hst''⟩
  · iframe #; iframe
  (try wp_auto)
  iunfold epConfState at Hcs
  icases Hcs with ⟨Hcs, #Hcsok⟩
  -- `select { case m := <-s.r.msgSnapC: ...; default: }`
  ihave #Hmscch := is_bag_is_chan γc msc Pm $$ Hmscb
  rw [isChanBag_unseal] at *
  iunfold isChanBagDef at Hmscb
  icases Hmscb with ⟨-, #Hinv⟩
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
      unfold nonblockingRecvAu nonblockingRecvAuInner
      isplit
      · iinv Hinv with Hi Hclose
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hmask
        inext
        unfold chanBagInv
        icases Hi with ⟨%st0, Hoc, Hi⟩
        iexists st0
        iframe Hoc
        rcases st0 with (_ | ⟨v, rest⟩) | _ | v | _ | _ | _ | (_ | ⟨_, _⟩)
        all_goals dsimp only
        case Buffered.cons | SndPending =>
          sorry -- SNAPSHOT-SORRY #7: the `msgSnapC` merge branch (a `MsgSnap` received: `createMergedSnapshotMessage`/`sendMergedSnap` over `rnSnapMsg`)
        all_goals first | itrivial | (iexfalso; iexact Hi)
      · itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- `default`
    (try wp_auto)
    ihave Hcs : epConfState ep cs' $$ [Hcs]
    · iunfold epConfState; iframe Hcs Hcsok
    ihave HtokR : srvTokRights E (ciEff γ st''.k) $$ [HtokR]
    · rw [Hst''.2]; iexact HtokR
    iapply HΦ
    iexists γ, TM, E, b, st'', ai', at', a', t', cs'
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
    ipureintro
    exact ⟨Hst''.1, hai', by rw [Hst''.2]; exact hci'.imp_left And.right, by rw [Hst''.2]; exact hciL, hat'⟩

end proof

end EtcdGrove
end Perennial
