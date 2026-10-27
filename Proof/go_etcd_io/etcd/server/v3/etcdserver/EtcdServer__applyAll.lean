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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  intro s γ ci TM E ρ γr b ep ap es ents ms f0 rac nc st ai at0 a t cs x A mst γs γp dv γnc w Hms Hai1
    Hok hEok hcap hdv haw
  wp_start as ⟨#Hsrv, #Hsa, #Hbw, #Hes, #Hrac, #Hracc, #Hsn, #Hnc, #Hncb, Hnrc, #Hesl, #Hentsat, Hai, Hat, Hcs,
    Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, HKV, Hao, #Hlog, #Hbc, #HW, #HWA, Hka, HRS, #Hkb, Hdv, #Hdvr, HAR⟩
  ihave #Hsrv' := Hsrv
  iunfold isServer at Hsrv'
  icases Hsrv' with ⟨-, -, ⟨%sv, #Hfl⟩, -, -⟩
  iunfold srvFieldsAt at Hfl
  icases Hfl with ⟨#Hlgf, %Hlgnn, -⟩
  ihave #Hsa' := Hsa
  iunfold isServerApplyAll at Hsa'
  icases Hsa' with ⟨%wt, %msc, %sc, #Hwtf, #Hwt, #Hmscf, ⟨%γc, %Pm, #Hmscb, #Hnosnap⟩, #Hsc,
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
  icases Hss with ⟨%sd0, %sm0, %sf0, Hsd0, Hsm0, Hsf0, %Hdm0, #Hmst, #Hro0, Hak0, %γss0, #Htinv0,
    #Hslb0⟩
  ihave Hfs : srvFS s $$ [Hsf0]
  · iunfold srvFS; iexists _; iexact Hsf0
  wp_apply hAE s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr A γp dv w Hms Hai1 Hok
    hEok hdv
    $$ [Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hao Hfs Hka HRS Hdv HAR]
    as ⟨Hfs, Hdv, HAR, %st', %ai', %at', %a', %t', %cs', Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, Hgr, Hao, #HWA',
      ⟨%x', HKV, %Hx', #Hlog', Hka, HRS⟩, %Hpost⟩
  · iframe #; iframe
  iunfold srvFS at Hfs
  icases Hfs with ⟨%sf1, Hsf1⟩
  obtain ⟨hok', hai', hlen', hci', hat'⟩ := Hpost
  have Hai' : uint.Z ai ≤ uint.Z ai' := by rw [hai']; exact Int.le_max_left _ _
  ihave Hss : srvSnapState s ep mst γs ai' (W64 0) $$ [Hsd0 Hsm0 Hsf1 Hak0]
  · iunfold srvSnapState; iexists _, _, _; iframe Hsd0 Hsm0 Hsf1 Hmst Hro0 Hak0
    isplitr
    · ipureintro; exact ⟨by have := Hdm0.1; omega, by have := Hdm0.2; omega⟩
    iexists γss0; iframe Htinv0 Hslb0
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
      iframe Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hbr HAR
      isplitl [Hao]
      · iexact Hao
      isplitr
      · iexact Hlb
      isplitr
      · iexact HWA'
      isplitl [HKV Hka HRS]
      · iexists x'; iframe HKV Hlog' Hka HRS; ipureintro; exact Hx'
      ipureintro; exact ⟨hok', hai', hci', hat'⟩
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
  iintro ⟨#Hflb, -⟩
  (try wp_auto)
  -- (D19i part 1) the storage's floor past the batch, so past the applied index
  ihave #Hfl' : memFloorAtLeast mst γs (uint.Z ai') $$ []
  · rw [hai']; iexact Hflb
  -- `s.snapshotIfNeededAndCompactRaftLog(ep)`
  wp_apply hSINC s E ρ.wait γ ci b γr ep st' ai' at' cs' a' t' x' mst γs γp
      (w + (unapplied ai ms).length) hok' hcap (by push_cast; omega)
    $$ [Hss Hai Hat Hcs Hst Hbe Happ Hlr HKV]
    as ⟨%st'', Hss, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, %Hst''⟩
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
        case Buffered.cons =>
          -- (D19p) nothing is ever sent on `msgSnapC`
          iintro -
          icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨Hv, -⟩
          iexfalso; iapply Hnosnap $$ Hv
        case SndPending =>
          iintro -
          iexfalso; iapply Hnosnap $$ Hi
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
    iframe Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hbr HAR
    isplitl [Hao]
    · iexact Hao
    isplitr
    · iexact Hlb
    isplitr
    · iexact HWA'
    isplitl [HKV Hka HRS]
    · iexists x'; iframe HKV Hlog' Hka HRS; ipureintro; exact Hx'
    ipureintro; exact ⟨Hst''.1, hai', by rw [Hst''.2]; exact hci', hat'⟩

end proof

end EtcdGrove
end Perennial
