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
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__createMergedSnapshotMessage
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__sendMergedSnap
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
    (hSINC : EtcdServer.snapshotIfNeededAndCompactRaftLog.spec (GF := GF) (hG := hG))
    (hCM : EtcdServer.createMergedSnapshotMessage.spec (GF := GF) (hG := hG))
    (hSM : EtcdServer.sendMergedSnap.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyAll.spec (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr b ep ap es ents ms f0 rac nc st ai at0 a t cs x Hms Hai1 Hok hEok
  wp_start as ⟨#Hsrv, #Hsa, #Hbw, #Hes, #Hrac, #Hsn, #Hnc, #Hncb, #Hesl, #Hentsat, Hai, Hat, Hcs,
    Hss, Hst, Hbe, Happ, Hlr, Hbr, HKV, Hao, #Hlog⟩
  ihave #Hsrv' := Hsrv
  iunfold isServer at Hsrv'
  icases Hsrv' with ⟨-, ⟨%sv, #Hfl⟩, -⟩
  iunfold srvFieldsAt at Hfl
  icases Hfl with ⟨#Hlgf, %Hlgnn, -⟩
  ihave #Hsa' := Hsa
  iunfold isServerApplyAll at Hsa'
  icases Hsa' with ⟨%wt, %msc, %sc, #Hwtf, #Hwt, #Hmscf, ⟨%γc, %Pm, #Hmscb⟩, #Hsc⟩
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, ⟨%g, #Hg, #Hgs⟩, ⟨%bsl, #Hbsl⟩⟩
  ihave #Pbe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  wp_auto
  -- `s.applySnapshot(ep, apply)`: no snapshot
  wp_apply hASnap s ep ap $$ []
  · iframe #
  (try wp_auto)
  -- `s.applyEntries(ep, apply)`
  wp_apply hAE s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr Hms Hai1 Hok hEok
    $$ [Hai Hat Hcs Hst Hbe Happ Hlr HKV Hao]
    as ⟨%st', %ai', %at', %a', %t', %cs', Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, Hao, ⟨%x', HKV, %Hx',
      #Hlog'⟩, %Hpost⟩
  · iframe #; iframe
  obtain ⟨hok', hai'⟩ := Hpost
  (try wp_auto)
  -- `backend.VerifyBackendConsistency(s.Backend(), s.Logger(), true, schema.AllBuckets...)`
  wp_apply hBk s $$ [Hbr] as %be Hbr
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
  iunfold srvAppliedOwn at Hao
  ihave #Hlb := monoNatLbOwn_get γr.applied _ _ $$ Hao
  iunfold isWaitTime at Hwt
  icases Hwt with ⟨%wi, %Hwi, -, #HTrig⟩
  subst Hwi
  wp_apply HTrig $$ []
  · iintro !>; iunfold appliedAtLeast; iexact Hlb
  (try wp_auto)
  -- `<-apply.notifyc`
  iunfold isUnitBag at Hncb
  icases Hncb with ⟨%γn, #Hncb⟩
  wp_apply wp_bag_receive γn nc (fun _ => iprop(True)) $$ [] as %u -
  · iexact Hncb
  (try wp_auto)
  -- `s.snapshotIfNeededAndCompactRaftLog(ep)`
  wp_apply hSINC s E γ ci b γr ep st' ai' at' cs' a' t' x' hok'
    $$ [Hss Hai Hat Hcs Hst Hbe Happ Hlr HKV]
    as ⟨%st'', Hss, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, %Hst''⟩
  · iframe #; iframe
  (try wp_auto)
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
          iintro Hoc
          icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨-, Hi⟩
          imod Hmask with -
          imod Hclose $$ [Hoc Hi] with -
          · inext; iexists .Buffered rest; iframe
          imodintro
          (try wp_auto)
          wp_apply hCM s v at' ai' cs' as %merged -
          (try wp_auto)
          wp_apply hSM s merged
          (try wp_auto)
          iapply HΦ
          iexists st'', ai', at', a', t', cs'
          iframe Hai Hat Hcs Hss Hst Hbe Happ Hlr Hbr
          isplitl [Hao]
          · iunfold srvAppliedOwn; iexact Hao
          isplitr
          · iunfold appliedAtLeast; iexact Hlb
          isplitl [HKV]
          · iexists x'; iframe HKV Hlog'; ipureintro; exact Hx'
          ipureintro; exact ⟨Hst''.1, hai'⟩
        case SndPending =>
          iintro Hoc
          imod Hmask with -
          imod Hclose $$ [Hoc] with -
          · inext; iexists .RcvCommit; iframe Hoc
          imodintro
          (try wp_auto)
          wp_apply hCM s v at' ai' cs' as %merged -
          (try wp_auto)
          wp_apply hSM s merged
          (try wp_auto)
          iapply HΦ
          iexists st'', ai', at', a', t', cs'
          iframe Hai Hat Hcs Hss Hst Hbe Happ Hlr Hbr
          isplitl [Hao]
          · iunfold srvAppliedOwn; iexact Hao
          isplitr
          · iunfold appliedAtLeast; iexact Hlb
          isplitl [HKV]
          · iexists x'; iframe HKV Hlog'; ipureintro; exact Hx'
          ipureintro; exact ⟨Hst''.1, hai'⟩
        all_goals first | itrivial | (iexfalso; iexact Hi)
      · itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- `default`
    (try wp_auto)
    iapply HΦ
    iexists st'', ai', at', a', t', cs'
    iframe Hai Hat Hcs Hss Hst Hbe Happ Hlr Hbr
    isplitl [Hao]
    · iunfold srvAppliedOwn; iexact Hao
    isplitr
    · iunfold appliedAtLeast; iexact Hlb
    isplitl [HKV]
    · iexists x'; iframe HKV Hlog'; ipureintro; exact Hx'
    ipureintro; exact ⟨Hst''.1, hai'⟩

end proof

end EtcdGrove
end Perennial
