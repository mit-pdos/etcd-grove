/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__scheduleCheckpointIfNeeded.lean` (pgaps,
2026-11-21: until then the trust boundary, an axiom, when the method was names only for its
`int64(le.checkpointInterval.Seconds())`; Perennial steps a float-to-integer conversion to an
arbitrary integer since 08d191151). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__scheduleCheckpointIfNeeded
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__getRemainingTTL
public import Spec.time.Duration__Seconds
public import Spec.container.heap.Push
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Duration
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Time__Add
public import Proof.go_etcd_io.etcd.server.v3.lease.QueueLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.scheduleCheckpointIfNeeded.wp_proof
    (hRem : lease.Lease.getRemainingTTL.spec (GF := GF) (hG := hG))
    (hSec : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (hLen : lease.LeaseQueue.Len.spec (GF := GF) (hG := hG))
    (hLess : lease.LeaseQueue.Less.spec (GF := GF) (hG := hG))
    (hSwap : lease.LeaseQueue.Swap.spec (GF := GF) (hG := hG))
    (hPush : lease.LeaseQueue.Push.spec (GF := GF) (hG := hG))
    (hHPush : heap.Push.spec (GF := GF) (hG := hG))
    (hDebug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hInt64 : zap.Int64.spec (GF := GF) (hG := hG))
    (hDur : zap.Duration.spec (GF := GF) (hG := hG))
    (hNow : _root_.Perennial.time.Now.spec (GF := GF) (hG := hG))
    (hAdd : _root_.Perennial.time.Time.Add.spec (GF := GF) (hG := hG)) :
    lease.lessor.scheduleCheckpointIfNeeded.spec (GF := GF) (hG := hG) := by
  intro lp l cp h hx id r t dq1 dq2 dq3
  haveI : go.NotInterface go.int64 := ⟨by simp [go.int64]⟩
  wp_start as ⟨#Hcfg, Hcp, Hh, Hhq, #HID, Hrem, Httl⟩
  ihave #Hheap : isPkgInit (PROP := IProp GF) pkg_id.container.heap $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  iunfold lessorCfg at Hcfg
  icases Hcfg with ⟨%mt, %cpp, %cl, %ci, %lg, %rr, -, -, -, -, #Hci, #Hlg, #Hlgok, -, -⟩
  wp_auto
  by_cases hcp : cp = func.nil
  · rw [decide_eq_true hcp]
    wp_auto
    iapply HΦ
    iframe Hcp Hrem Httl
    iexists h, hx
    iframe
  rw [decide_eq_false hcp]
  wp_auto
  wp_apply (hRem l r t dq2 dq3) $$ [$Hpkg $Hrem $Httl] as ⟨Hrem, Httl⟩
  wp_method_call
  wp_auto
  wp_apply hSec as %f -
  wp_apply wp_ArbitraryInt as %x -
  try wp_auto
  by_cases Hgt : sint.Z x < sint.Z (if 0 < sint.Z r then r else t)
  all_goals first | simp only [decide_eq_true Hgt] | simp only [decide_eq_false Hgt]
  all_goals (wp_pures; try wp_auto)
  · wp_join iprop(le_ptr ↦ lp ∗ lease_ptr ↦ l) with [le lease] as ⟨le, lease⟩
    · icases Hlgok with (%Hn | #Hz)
      · exfalso; simp_all
      (try wp_auto)
      wp_apply hInt64 as %f1 -
      (try wp_auto)
      wp_apply hDur as %f2 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply hDebug $$ []
      · iframe #
      wp_join_done
    (try wp_auto)
    wp_apply hNow as %tn -
    (try wp_auto)
    wp_apply hAdd as %ta -
    (try wp_auto)
    wp_alloc it as Hit
    iStructNamed Hit
    ipersist id
    (try wp_auto)
    ihave #Hiface := queue_heapIface hLen hLess hSwap hPush (lF go!"leaseCheckpointHeap" lp) $$ Hpkg
    wp_apply (hHPush (Loc × w64) (interface.mk (go.GoType.PointerType LeaseQueue.ty)
        #(lF go!"leaseCheckpointHeap" lp)) (queueHeap (lF go!"leaseCheckpointHeap" lp)) queueElem hx
        (interface.mkOk (go.GoType.PointerType LeaseWithTime.ty) #it) (it, id))
      $$ [$Hheap $Hiface Hh Hhq id time index] as ⟨%ys, Hys, -⟩
    · isplitl [Hh Hhq]
      · iunfold queueHeap; iexists h; iframe
      iunfold queueElem
      isplitr
      · ipureintro; rfl
      iexists _
      iunfold lwtAt
      simp only
      iframe id index
      iexists _
      iexact time
    (try wp_auto)
    iapply HΦ
    iunfold queueHeap at Hys
    icases Hys with ⟨%s', Hq', Hqa'⟩
    iframe Hcp Hrem Httl
    iexists s', ys
    iframe
  · iapply HΦ
    iframe Hcp Hrem Httl
    iexists h, hx
    iframe

end proof

end EtcdGrove
end Perennial
