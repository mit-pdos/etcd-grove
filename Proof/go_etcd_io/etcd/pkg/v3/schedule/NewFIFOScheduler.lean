/-
`schedule.NewFIFOScheduler`. Lean-first (2026-10-22, the scheduler translated with its body; until
then a trust-boundary axiom).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewFIFOScheduler
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.fifo__run
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Assert
public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Chain
public import Proof.go_etcd_io.etcd.pkg.v3.schedule.WithCancel

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3 schedule

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

/-- The scheduler's names allocated (the queue `[n, p₀]`: the stop token's name and the initial
`True`), its context made (done once the `stopped` flag is set), its lock invariant and channel
invariants set up, and the worker forked with its resources. -/
theorem schedule.NewFIFOScheduler.wp_proof
    (wp_Assert : verify.Assert.spec (GF := GF) (hG := hG))
    (wp_run : schedule.fifo.run.spec (GF := GF) (hG := hG)) :
    schedule.NewFIFOScheduler.spec (GF := GF) (hG := hG) := by
  intro lg Pay
  wp_start as %Hlg
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hver : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify $$ []
  · iPkgInit
  (try wp_auto)
  have hlg : decide (lg = null) = false := decide_eq_false Hlg
  simp only [hlg, Bool.not_false]
  wp_apply wp_Assert
  wp_apply chan.wp_make2 (V := Unit) (W64 1) as %rch %γr ⟨#Hrch, %Hrcap, Hroc⟩
  · ipureintro; decide
  wp_apply chan.wp_make2 (V := Unit) (W64 1) as %dch %γd ⟨#Hdch, %Hdcap, Hdoc⟩
  · ipureintro; decide
  (try wp_auto)
  iStructNamed «$r0»
  wp_apply sync.wp_NewCond (interface.mk (go.GoType.PointerType sync.Mutex.ty) #(fifoMu «$r0_ptr»))
    as %cnd #Hcnd
  imod dghostVar_alloc (A := Bool) false with ⟨%st, Hst⟩
  imod savedProp_alloc (GF := GF) Pay with ⟨%pay, #Hpay⟩
  wp_apply context.wp_Background
  wp_apply wp_WithCancel_Background_nn
      iprop(dghostVar st DFrac.discard true ∗ ∃ P : IProp GF, savedProp pay P ∗ □ P) $$ []
    as %ctx %γc %cf ⟨%Hcfnn, #Hcancel, #Hisctx⟩
  · iframe #
    iapply _root_.Perennial.context.isClosedchanInit_of_init $$ Hctxp
  (try wp_auto)
  -- the ghost state: the run token, the queue `[n, p₀]`, the worker's state and tokens
  imod dghostVar_alloc (A := Unit) () with ⟨%run, Hrun⟩
  imod dghostVar_alloc (A := Unit) () with ⟨%n, Hn⟩
  imod savedProp_alloc (GF := GF) iprop(True) with ⟨%p0, #Hp0⟩
  imod mono_list_own_alloc (GF := GF) [n, p0] with ⟨%jobs, Hq, #Hlb⟩
  imod dghostVar_alloc (A := RunSt) RunSt.idle with ⟨%w, Hw⟩
  imod dghostVar_alloc (A := Unit) () with ⟨%rc, Hrc⟩
  imod dghostVar_alloc (A := Unit) () with ⟨%dc, Hdc⟩
  imod dghostVar_alloc (A := Unit) () with ⟨%dr, Hdr⟩
  ihave ⟨Hq1, Hq2⟩ := (monoListAuthOwn_fractional jobs [n, p0]).fractional (1 : Qp).half
    (1 : Qp).half |>.1 $$ [Hq]
  · rw [Qp.half_add_half]; iexact Hq
  ihave ⟨Hw1, Hw2⟩ := dghostVar_split w RunSt.idle (DFrac.own (1 : Qp).half)
    (DFrac.own (1 : Qp).half) $$ [Hw]
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hw
  ipersist resume
  ipersist donec
  ipersist ctx
  ipersist finishCond
  ipersist lg
  let γ : SchedNames := ⟨run, jobs, pay⟩
  let F : FifoNames := ⟨w, st, rc, dc, dr, rch, γr, dch, γd, ctx, γc, cf, cnd, lg⟩
  imod inv_alloc resumeN ⊤ (resumeInv (GF := GF) F) $$ [Hroc] with #Hrinv
  · inext; iunfold resumeInv; iexists []; ileft; iexact Hroc
  imod inv_alloc donecN ⊤ (donecInv (GF := GF) γ F) $$ [Hdoc] with #Hdinv
  · inext; iunfold donecInv; ileft; iexact Hdoc
  imod sync.init_Mutex (fifoLockInv «$r0_ptr» γ F) ⊤ (fifoMu «$r0_ptr») $$ mu
    [pendings scheduled finished cancel Hw1 Hq1 Hst] with #Hmu
  · inext
    iunfold fifoLockInv
    iexists slice.nil, [], [], RunSt.idle, [n, p0], 1, cf, W64 0, W64 0
    simp only [named]
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · ipureintro; exact ⟨rfl, chainOk_nil (L := [n, p0]) (by simp)⟩
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; itrivial
    isplitl []
    · iunfold batonAt
      iunfold baton
      iexists p0, iprop(True)
      iframe #
      ipureintro; rfl
    ileft
    iframe
    ipureintro; rfl
  ihave #Hfifo : fifoIs «$r0_ptr» γ F $$ []
  · iunfold fifoIs
    simp only [named]
    iframe #
    isplitl []
    · unfold fifoCtxDesc stopped schedPay; iexact Hisctx
    isplitl []
    · unfold stopped schedPay; iexact Hcancel
    ipureintro; exact Hcfnn
  -- `go f.run()`: the worker, with its resources and its own thread token
  wp_apply wp_fork_tok_body $$ [Hrun Hw2 Hrc Hdc Hdr]
  · iintro Htok
    wp_apply wp_run «$r0_ptr» γ F $$ [Hrun Hw2 Hrc Hdc Hdr Htok] as Htok
    · iframe #
      iunfold workerRes
      iunfold schedRunning
      iframe
    iframe
    ipureintro; exact isPanic_intoVal _
  (try wp_auto)
  iapply HΦ
  iexists γ, n, p0
  isplitl []
  · iunfold isFifo
    isplitr
    · ipureintro; simp [interface.mkOk]
    isplitl []
    · iexists [n, p0]; iexact Hlb
    iunfold isFifoOf
    iunfold fifoOf
    iexists «$r0_ptr», F
    iframe #
    ipureintro; rfl
  isplitl [Hn]
  · iunfold schedStopTok
    iexists n
    iframe
    iunfold schedStopName
    iapply monoListIdxOwn_get 0 n rfl $$ Hlb
  iunfold schedQueue
  iframe
  iframe #
  iunfold schedPayIs
  iexact Hpay

end proof

end EtcdGrove
end Perennial
