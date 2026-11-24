/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/newLessor.lean`. Lean-first (no Rocq counterpart);
prove-ps2-newlessor5, 2026-11-21.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.newLessor
public import Spec.go_etcd_io.etcd.server.v3.lease.newLeaseExpiredNotifier
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__initAndRecover
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__runLoop
public import Proof.go_etcd_io.etcd.server.v3.lease.NewLessorAlloc
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorMuFrac
public import Proof.go_etcd_io.etcd.server.v3.lease.NotifCell
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LessorApplyReal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem lease.newLessor.wp_proof
    (hNE : lease.newLeaseExpiredNotifier.spec (GF := GF) (hG := hG))
    (hIR : lease.lessor.initAndRecover.spec (GF := GF) (hG := hG))
    (hRun : lease.lessor.runLoop.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    lease.newLessor.spec (GF := GF) (hG := hG) := by
  intro lg cl cfg d W Pk qo GA S r mono recs reqOf Lr hS hlp hrecs hrq hLr
  wp_start as ⟨Hlg, %Hrate, #Hcl, #HB, Ho, Htoks, Hrb, #HGA, %Htb⟩
  ihave Hli : (leaseInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hli with ⟨-, -, -, ⟨#Hfor, #Hdrr, -, -, ⟨%dci, #Hdci⟩, ⟨%dri, #Hdri⟩⟩, -⟩
  (try wp_auto)
  wp_join iprop(∃ ci : _root_.Perennial.time.Duration, "checkpointInterval" ∷ checkpointInterval_ptr ↦ ci)
    with [checkpointInterval] as ⟨%ci, checkpointInterval⟩
  wp_join iprop(∃ ri : _root_.Perennial.time.Duration,
      "expiredLeaseRetryInterval" ∷ expiredLeaseRetryInterval_ptr ↦ ri)
    with [expiredLeaseRetryInterval] as ⟨%ri, expiredLeaseRetryInterval⟩
  wp_join iprop(∃ rr : w64, "leaseRevokeRate" ∷ leaseRevokeRate_ptr ↦ rr ∗ "%Hrr" ∷ ⌜0 < sint.Z rr⌝)
    with [leaseRevokeRate] as ⟨%rr, leaseRevokeRate, %Hrr⟩
  · iexists _; iframe; ipureintro; decide
  · iexists _; iframe; ipureintro
    have h0 : sint.Z cfg.leaseRevokeRate' ≠ 0 := fun h => Hif (by word)
    omega
  (try wp_auto)
  wp_apply (wp_map_make1 (V := Loc) LeaseID.ty (go.GoType.PointerType Lease.ty)) as %lm HM
  wp_apply (wp_map_make1 (V := w64) LeaseItem.ty LeaseID.ty) as %im HI
  wp_apply hNE as %np Hnp
  wp_apply (wp_slice_make2 (V := Loc) (W64 0)) as %h ⟨Hh, Hhc⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply (chan.wp_make2 (V := GoSlice) (W64 16)) as %ec %γec ⟨#Hec, %_, Heco⟩
  · ipureintro; decide
  wp_apply (chan.wp_make1 (V := Unit)) as %sc %γsc ⟨#Hsc, %_, Hsco⟩
  wp_apply (chan.wp_make1 (V := Unit)) as %dc %γdc ⟨#Hdc, %_, Hdco⟩
  (try wp_auto)
  irename «$r0» => Hl
  generalize «$r0_ptr» = lp at *
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  iStructNamed Hl
  ipersist minLeaseTTL
  ipersist expiredC
  ipersist stopC
  ipersist doneC
  ipersist checkpointPersist
  ipersist cluster
  ipersist checkpointInterval
  ipersist lg
  ipersist leaseRevokeRate
  ipersist expiredLeaseRetryInterval
  -- `le.initAndRecover()`
  ihave Hq : queueAt (GF := GF) h [] 1 $$ [Hh Hhc]
  · iunfold queueAt; iframe Hhc; simp only [List.map_nil, List.replicate_zero]; iframe Hh
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
  have hS' : S mvcc.leaseName := hS
  have hrecs' : backend.bktEnts ((r.lookup mvcc.leaseName).getD ∅) = recs.map leaseRecEnc := hrecs
  wp_apply (hIR lp lm np h [] cfg.MinLeaseTTL' d.γB d.P W Pk d.be qo S r recs hS' hlp hrecs')
    $$ [$Hpkg $b $leaseMap $HM $minLeaseTTL $leaseExpiredNotifier $Hnp $leaseCheckpointHeap $Hq $HB $Ho
      $Htoks $Hrb]
    as ⟨%ls, %h', %hx', %Hlen, Hb, Hlm, HM, Hrl, #Hr, Hnp, Hnot, Hh, Hhq, Ho, Hrb⟩
  -- the ghost state, `le.mu`, the channels' idioms
  have hnd : (recs.map (·.1)).Nodup := leaseRecs_nodup _ recs hrecs
  ihave demotec : lF go!"demotec" lp ↦ (chan.nil : GoChan) $$ [demotec]
  · rw [show (chan.nil : GoChan) = null from rfl]; iexact demotec
  imod (newLessor_alloc lp lm im np h' hx'
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)
      cfg.MinLeaseTTL' ec sc dc γec γsc γdc GA mono recs ls reqOf Lr Hnn Hlen hnd hrq hLr)
    $$ [$mu $demotec $Hlm $HM $itemMap $HI $rd $cp $Hb $Hnp $Hnot $Hh $Hhq $expiredC $Hec $Heco $stopC
      $Hsc $Hsco $doneC $Hdc $Hdco $Hrl $Hr $HGA]
    with ⟨%γl, #Hinv, #Hmode, #Hexp, #Hguard, Hrds, Hown, Hwt, Hever, Hrvk, Hrdo, Hbh, Hstop, #Hstr,
      #Hreq, #Hat, Hntok, Hdone⟩
  ihave #Hcfg : lessorCfg (GF := GF) lp $$ [Hlg]
  · iunfold lessorCfg
    iexists cfg.MinLeaseTTL', cfg.CheckpointPersist', cl, ci, lg, rr
    iframe minLeaseTTL checkpointPersist cluster Hcl checkpointInterval lg leaseRevokeRate
    isplitl [Hlg]
    · icases Hlg with (%Hn | #Hz)
      · ileft; ipureintro; exact Hn
      · iright; iexact Hz
    ipureintro; exact Hrr
  ihave #Hinv' := Hinv
  iunfold lessorInv at Hinv'
  icases Hinv' with ⟨-, #Hpin, -, -⟩
  -- the reader slots: one for the loop, the rest the caller's
  have hmax : sync.rwmutex.actualMaxReaders.toNat =
      (sync.rwmutex.actualMaxReaders.toNat - 1) + 1 := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; decide
  ihave ⟨Hrd1, Hrds⟩ : iprop(lessorRd (GF := GF) lp γl ∗
      [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 1) (), lessorRdOf γl)
      $$ [Hrds]
  · rw [hmax, List.replicate_succ]
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hrds with ⟨Hrd1, Hrds⟩
    rw [← hmax]
    iframe Hrd1
    iapply (BigSepL.bigSepL_impl (PROP := IProp GF)) $$ Hrds
    iintro !> %k %x %_ H
    iunfold lessorRdOf; iexists lp; iframe Hpin H
  -- the backend's contract
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave #Happly := lessorApplyOk_real hBT hLI hUP hUL hID hName hSafe lp $$ [$Hbpkg $Hspkg]
  (try wp_auto)
  -- `go le.runLoop()`
  wp_apply wp_fork_tok_body $$ [Hrd1 Hntok Hdone]
  · iintro Htok
    icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨H0, Hrest⟩
    (try wp_auto)
    wp_apply (hRun lp γl GA ri dc γdc)
      $$ [$Hpkg $Hinv $Hcfg $Hexp $Hguard $Hstr $expiredLeaseRetryInterval $doneC $Hdone $Hrd1 $Hntok $H0]
      as H0
    · ipureintro; exact Htb
    isplitr
    · ipureintro; simp [val.isPanic]
    iapply (threadTok_level0 (GF := GF)).2; iframe
  (try wp_auto)
  iapply HΦ
  iframe Ho
  isplitl [Hrb]
  · rw [show (go!"lease" : GoString) = mvcc.leaseName from rfl]; iexact Hrb
  iexists γl
  iframe Hinv Hmode Hcfg minLeaseTTL Hexp Hguard Hrds Hown Hwt Hever Hrvk Hrdo Happly Hstop Hreq
  isplitl [Hbh]
  · iunfold lessorBeOn; iexact Hbh
  iexists ls
  iframe Hat
  ipureintro; exact Hlen

end proof

end EtcdGrove
end Perennial
