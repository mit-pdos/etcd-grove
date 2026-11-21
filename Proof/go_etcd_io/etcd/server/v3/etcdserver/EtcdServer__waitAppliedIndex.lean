/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__waitAppliedIndex.lean`:
`s.waitAppliedIndex()` (`v3_server.go`), a `select` over `s.ApplyWaitCommit()` (stepped into:
`s.applyWait.Wait(s.getCommittedIndex())`, over the read side's `isWaitTime`), `s.stopping` (the
server's stop channel) and `time.After(applyTimeout)` (Perennial's bag of times): `nil`,
`ErrStopped` or `ErrTimeoutWaitAppliedIndex`, `errors.New` errors (`applyErrIs`). Lean-first; until
prove-etcdserver (2026-11-20) a names-only contract (the lease-renew plan's C3, 2026-11-01).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__waitAppliedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getCommittedIndex
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Inv

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

theorem EtcdServer.waitAppliedIndex.wp_proof
    (hGCI : EtcdServer.getCommittedIndex.spec (GF := GF) (hG := hG)) :
    EtcdServer.waitAppliedIndex.spec (GF := GF) (hG := hG) := by
  intro s E ρ γr
  wp_start as ⟨#Hreq, #Hrd⟩
  iunfold isServerReadM at Hrd
  icases Hrd with ⟨%v, #Hw⟩
  iunfold srvReadFieldsAtM at Hw
  icases Hw with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HCI, #Haw, #HisW, -, -, #Hstf,
    #Hstc, -⟩
  -- the error variables: `ErrStopped` (the server's fact), `ErrTimeoutWaitAppliedIndex` (its package's)
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨-, -, -, -, ⟨-, -, #HStop, -⟩⟩, -⟩
  ihave ⟨%eStop, #HeStop, #HaStop⟩ := errVarLeaf_get _ $$ HStop
  ihave #Herr : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors $$ []
  · iPkgInit
  ihave Hei : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Herr
  icases Hei with ⟨-, #Hev, -⟩
  ihave #NTW := EtcdGrove.errorsNewVars_mem
    (X := go_etcd_io.etcd.server.v3.etcdserver.errors.ErrTimeoutWaitAppliedIndex)
    (m := go!"etcdserver: request timed out, waiting for the applied index took too long")
    (by unfold go_etcd_io.etcd.server.v3.etcdserver.errors.errorsMsgs; simp) $$ Hev
  ihave #LTW := EtcdGrove.errVarLeaf_of_newVar _ _ $$ NTW
  ihave ⟨%eTW, #HeTW, #HaTW⟩ := errVarLeaf_get _ $$ LTW
  iunfold stopChan at Hstc
  icases Hstc with ⟨%γst, #Hstc⟩
  wp_auto_lc 2
  -- `s.ApplyWaitCommit()`: `s.applyWait.Wait(s.getCommittedIndex())` (stepped into before the
  -- wait's contract is unfolded: `wp_method_call` rewrites the first method call it finds)
  wp_method_call
  wp_call
  (try wp_auto)
  iunfold isWaitTime at HisW
  icases HisW with ⟨%wi, %Hwi, #HW, -⟩
  wp_apply hGCI s γr none $$ [] as %ci ⟨-, -, -⟩
  · iframe #
    simp only [srvCommittedOwnOpt]
    itrivial
  rw [Hwi]
  (try wp_auto)
  wp_apply HW $$ %ci as %awc ⟨%Qaw, #Hawc, -⟩
  (try wp_auto)
  ihave #Hawc' : (bcastOrClosed awc Qaw : IProp GF) $$ []
  · unfold bcastOrClosed bcastChan
    iunfold waitBcast at Hawc
    iexact Hawc
  icases bcastOrClosed_receive _ _ $$ Hawc' with ⟨%γaw, #Hawch, #Hawr⟩
  wp_apply (time.After.spec_pkgInit time.wp_After _) as %tch %γa #Htch
  (try wp_auto)
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the applied index reached the committed one: `nil`
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, awc, γaw
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hawch
    iapply Hawr
    iintro -
    wp_auto
    iapply HΦ
    ileft; ipureintro; rfl
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `s.stopping`: `ErrStopped`
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, v.stopping, γst
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownStopChan_is_chan $$ Hstc
    iapply stop_chan_receive _ _ _ _ _ $$ Hstc
    iintro ⟨-, -⟩
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexact HaStop
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the timeout: `ErrTimeoutWaitAppliedIndex`
    simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γa
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Htch
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
    inext
    iintro %t -
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexact HaTW
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
