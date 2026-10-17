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
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.toApply__notifyApplyCompleted
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
    (hNAC : toApply.notifyApplyCompleted.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyAll.spec (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr b ep ap es ents ms f0 rac P st ai at0 a t cs x A Hms Hai1 Hok hEok
  wp_start as ⟨#Hsrv, #Hsa, #Hbw, #Hes, #Hrac, #Hsn, Hsync, #Hesl, #Hentsat, Hai, Hat, Hcs,
    Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, HKV, Hao, #Hlog, #Hbc, HW, Hka, #Hkb⟩
  iunfold taSyncOk at Hsync
  icases Hsync with ⟨%w, %rsc, %γrs, %f, %acc, #Hw, #Hrsc, #Hrsb, #Hf, #Hfok, HP, #Hacc, Hdone⟩
  ihave #Hsrv' := Hsrv
  iunfold isServer at Hsrv'
  icases Hsrv' with ⟨-, -, ⟨%sv, #Hfl⟩, -, -⟩
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
  -- (etcd-io/etcd#22223) `if apply.waitForStorageBeforeApply { <-apply.raftStorageReadyC }`
  wp_join with [ep apply]
  · wp_apply wp_broadcast_receive rsc γrs iprop(True) .Unknown $$ [$Hrsb]
    (try wp_auto)
    wp_join_done
  -- `s.applySnapshot(ep, apply)`: no snapshot
  wp_apply hASnap s ep ap $$ []
  · iframe #
  (try wp_auto)
  -- `s.applyEntries(ep, apply)`
  wp_apply hAE s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr A Hms Hai1 Hok hEok
    $$ [Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hao HW Hka]
    as ⟨%st', %ai', %at', %a', %t', %cs', Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, Hgr, Hao, ⟨%x', HKV, %Hx',
      #Hlog', Hka⟩, %Hpost⟩
  · iframe #; iframe
  obtain ⟨hok', hai', hci'⟩ := Hpost
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
  icases srvAppliedOwn_lb γr ai' $$ Hao with ⟨Hao, #Hlb⟩
  iunfold isWaitTime at Hwt
  icases Hwt with ⟨%wi, %Hwi, -, #HTrig⟩
  subst Hwi
  wp_apply HTrig $$ []
  · iintro !>; iexact Hlb
  (try wp_auto)
  -- `if !apply.waitForStorageBeforeApply { <-apply.raftStorageReadyC }`
  rw [show (!w) = decide (w = false) from by cases w <;> rfl]
  wp_join with [ep apply]
  · wp_apply wp_broadcast_receive rsc γrs iprop(True) .Unknown $$ [$Hrsb]
    (try wp_auto)
    wp_join_done
  -- `apply.notifyApplyCompleted()`
  wp_apply hNAC ap f acc P $$ [HP Hdone]
  · iframe #; iframe
  (try wp_auto)
  -- `s.snapshotIfNeededAndCompactRaftLog(ep)`
  wp_apply hSINC s E ρ.wait γ ci b γr ep st' ai' at' cs' a' t' x' hok'
    $$ [Hss Hai Hat Hcs Hst Hbe Happ Hlr HKV]
    as ⟨%st'', Hss, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, %Hst''⟩
  · iframe #; iframe
  (try wp_auto)
  iapply HΦ
  iexists st'', ai', at', a', t', cs'
  iframe Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hbr
  isplitl [Hao]
  · iexact Hao
  isplitr
  · iexact Hlb
  isplitl [HKV Hka]
  · iexists x'; iframe HKV Hlog' Hka; ipureintro; exact Hx'
  ipureintro; exact ⟨Hst''.1, hai', by rw [Hst''.2]; exact hci'⟩

end proof

end EtcdGrove
end Perennial
