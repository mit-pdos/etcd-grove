/- Lean-first (no Rocq counterpart). The proof of `runChecks`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.runChecks
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.newHistory
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.reader
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.watchCheck__register
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.watchCheck__receive
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.watchCheck__complete
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.noCluster__Version
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.RunChecksBackend
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.RunChecksWriter
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.RunChecksJoin
public import Spec.go_uber_org.zap.NewNop
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__SetTxPostLockInsideApplyHook
public import Spec.go_etcd_io.etcd.server.v3.lease.NewLessor
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorContract
public import Perennial.Proof.sync.WaitGroupJoin

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem runChecks.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hrecv : mvcc.api.wsChan_recv.law (GF := GF) (hG := hG))
    (halloc : mvccW_alloc.law (GF := GF))
    (hfresh : mvccImage_fresh.law (GF := GF))
    (hopen : etcdStorage_open.law (GF := GF))
    (hrest : backendRest_open.law (GF := GF))
    (hRdSplit : mvcc.api.mvccReaders_split.law (GF := GF))
    (hCR : mvcc.api.mvccClosed_rest.law (GF := GF))
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_bNew : backend.New.spec (GF := GF) (hG := hG))
    (wp_SetHook : backend.backend.SetTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG))
    (wp_NewLessor : lease.NewLessor.spec (GF := GF) (hG := hG))
    (wp_GetLease : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (wp_Attach : lease.lessor.Attach.spec (GF := GF) (hG := hG))
    (wp_Detach : lease.lessor.Detach.spec (GF := GF) (hG := hG))
    (wp_SRD : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG))
    (wp_mNew : mvcc.api.New.spec (GF := GF) (hG := hG))
    (wp_Version : noCluster.Version.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_newHistory : newHistory.spec (GF := GF) (hG := hG))
    (wp_run : writer.run.spec (GF := GF) (hG := hG))
    (wp_reader : reader.spec (GF := GF) (hG := hG))
    (wp_register : watchCheck.register.spec (GF := GF) (hG := hG))
    (wp_receive : watchCheck.receive.spec (GF := GF) (hG := hG))
    (wp_complete : watchCheck.complete.spec (GF := GF) (hG := hG)) :
    runChecks.spec (GF := GF) (hG := hG) := by
  intro cfg _ _ hops0 hops hrd0 hrd hw0 hw hckpt hdbo
  haveI := fun kv γ => hpers.1 kv γ
  haveI := fun ws γ ι => hpers.2.1 ws γ ι
  haveI := fun B f => hpers.2.2.2.1 B f
  wp_start as ⟨Hfile, #Hks, Htok, #Hvoff⟩
  haveI : ThreadBoundLe GF (2 ^ 29) := ⟨ThreadBoundLe.le_of (2 ^ 28) (by omega)⟩
  wp_auto
  wp_apply wp_NewNop as %lg #Hlgz
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlgz
  (try wp_auto)
  wp_apply wp_DefaultBackendConfig as %bc %Hbc
  (try wp_auto)
  obtain ⟨hlim, hhooks⟩ := Hbc
  imod halloc with ⟨%gx, Hreg, HW⟩
  wp_apply (wp_bNew _ (rcP bc.BatchLimit') ∅ (fun _ => mvccW gx) (fun _ => iprop(True))
      backend.bFresh) $$ [Hfile HW Htok] as %r Hr
  · iframe Hfile Htok Hvoff
    isplitr
    · ipureintro
      refine ⟨rcP_wf _ (by rw [hlim]; decide) (by rw [hlim]; decide), rfl⟩
    isplitr
    · iunfold backend.hooksOk
      iintro !> %γ %b %t _ _
      iunfold backend.hooksSpec
      ileft; ipureintro; exact hhooks
    · iintro %γ ⟨-, Hf⟩
      imodintro
      iframe HW Hf
  icases Hr with (⟨%b, %γB, %Hr, Hnew, #Hhooks, #Hbf, -⟩ | %Hpan)
  rotate_left
  · -- `backend.New` panics only where bbolt's `Open` failed, which `dbOpenOk` excludes
    exact absurd hdbo Hpan.1
  subst Hr
  (try wp_auto)
  -- the store's part of the backend opened; the client's rest
  have hRB : receiptBound GF ≤ 2 ^ 38 := ReceiptBoundLe.le (2 ^ 38)
  have hm : receiptBound GF + (sint.nat cfg.Ops' + 2) + 2 ≤ backend.wbInit := by
    unfold backend.wbInit
    have : sint.nat cfg.Ops' = (sint.Z cfg.Ops').toNat := rfl
    omega
  imod rc_open hfresh hopen hrest hCR γB b gx bc.BatchLimit' (sint.nat cfg.Ops' + 2) hm
    $$ [Hks Hreg Hnew] with Hbk
  · iframe Hks Hreg Hnew
  iunfold rcBk at Hbk
  icases Hbk with ⟨Hsf, #Hisb, Hhk, Hrbo, Hoh, Hor, Hrt, Hwm, #Hsc, Hcen⟩
  icases ownToks_add_1 2 (sint.nat cfg.Ops') γB.wb $$ Hwm with ⟨Hwops, Hw2⟩
  icases ownToks_add_1 1 1 γB.wb $$ Hw2 with ⟨Hw1, Hw1'⟩
  ihave Hw1 : backend.wbTok (GF := GF) γB $$ [Hw1]
  · unfold backend.wbTok; iexact Hw1
  ihave Hw1' : backend.wbTok (GF := GF) γB $$ [Hw1']
  · unfold backend.wbTok; iexact Hw1'
  -- `lease.NewLessor(lg, be, noCluster{}, …)`
  ihave #Hcl : lease.clusterOk (GF := GF) (interface.mkOk noCluster.ty #(zero_val noCluster)) $$ []
  · iunfold lease.clusterOk
    iexists _
    isplitr
    · ipureintro; rfl
    iintro !> %Φ' !> - HΦ'
    wp_apply wp_Version as %v %Hv
    iapply HΦ'
    ileft; ipureintro; exact Hv
  -- (mvccfull's Freeze, 2026-11-10) `NewLessor.spec` over a bucket of records, at none: the fresh
  -- file's `Lease` bucket is empty
  have hLe : ((backend.rbData (rcP bc.BatchLimit') ∅).lookup go!"lease").getD ∅ = ∅ := rfl
  have hrecs : backend.bktEnts (((backend.rbData (rcP bc.BatchLimit') ∅).lookup go!"lease").getD ∅) =
      ([] : List (w64 × w64 × w64)).map lease.leaseRecEnc := by
    rw [hLe]; simp [backend.bktEnts]
  wp_apply (wp_NewLessor lg _ _ (rcKB γB b gx bc.BatchLimit') (mvccW gx) iprop(True) (1 : Qp).half
      (fun _ => iprop(True)) (fun _ => True) (backend.rbData (rcP bc.BatchLimit') ∅) false
      [] (fun _ => W64 0) [] trivial (rcP_lease _) hrecs (by simp) (List.Perm.refl _))
    $$ [Hoh Hw1 Hrbo]
    as %l ⟨Hoh, Hrbo, %lp, %γl, %Hl, #Hlinv, #Hmode, #Hlcfg, -, #Hexp, #Hguard, Hlrds, Hlown, Hever,
      Hrvk, Hrdo, #Hckpt, Hbeon, #Happly, Hstop, -, -, #Hlookup⟩
  · rw [rcKB_P, rcKB_γB, rcKB_be]
    iframe Hcl Hisb Hoh Hw1
    isplitr
    · iright; iexact Hlgz
    isplitr
    · ipureintro; exact hckpt
    isplitr
    · ipureintro; simp only; exact Int.le_refl _
    isplitl [Hrbo]
    · iunfold backend.rbOwn at Hrbo; iexact Hrbo
    imodintro; rw [List.map_nil]; iapply BigSepL.bigSepL_nil.2; itrivial
  try rw [hLe]
  rw [List.map_nil]
  (try wp_auto)
  subst Hl
  -- two of the lessor's reader slots: the store's, the writer's
  obtain ⟨nl, hnl⟩ : ∃ nl, Int.toNat sync.rwmutex.actualMaxReaders = 2 + nl :=
    ⟨Int.toNat sync.rwmutex.actualMaxReaders - 2, by have := sync.actualMaxReaders_ge_2; omega⟩
  rw [hnl]
  icases (backend.bigSepL_replicate_add _ 2 nl).1 $$ Hlrds with ⟨Hlrd2, -⟩
  rw [List.replicate_succ, List.replicate_one]
  icases BigSepL.bigSepL_cons.1 $$ Hlrd2 with ⟨Hlrd1, Hlrd2⟩
  ihave Hlrd2 := (BigSepL.bigSepL_singleton (PROP := IProp GF)).1 $$ Hlrd2
  ihave #HisL := lease.isLessor_of_lessorInv wp_GetLease wp_Attach wp_Detach wp_SRD lp γl $$ [Hlinv]
  · iframe Hlinv; iPkgInit
  -- `mvcc.New(lg, be, le, mvcc.StoreConfig{})`
  rw [show (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b :
      GoInterface) = storageVal (etcdStorage (rcKB γB b gx bc.BatchLimit')) from (etcdStorage_val (rcKB γB b gx bc.BatchLimit')).symm]
  have hbl : mvcc.batchLimitOk
      (zero_val go_etcd_io.etcd.server.v3.storage.mvcc.StoreConfig).CompactionBatchLimit' := by
    rw [show (zero_val go_etcd_io.etcd.server.v3.storage.mvcc.StoreConfig).CompactionBatchLimit' =
      W64 0 from rfl]
    unfold mvcc.batchLimitOk mvcc.rangeLimitMax
    exact ⟨by decide, by decide⟩
  -- (mvccfull's Freeze, 2026-11-10) `New.spec` on any image, here the fresh one: the lessor's
  -- owner part (`Hlown`, no lease) lent and given back
  wp_apply (wp_mNew lg _ _ (etcdStorage (rcKB γB b gx bc.BatchLimit')) iprop(True) γl func.nil
      mvccStart false [] (DFrac.own 1) func.nil iprop(True) iprop(True) iprop(True) iprop(True)
      iprop(True)) $$ [Hsf Hlrd1 Hrdo Hlown]
    as %wsl ⟨%γk, %Hγl, #Hkv, Hσ, Hopn, Hmb, Hrdrs, ⟨%rd, Hrdo, Hdel⟩, Hlown, -, -⟩
  · iframe Hsf Hlrd1 HisL Hrdo Hlown
    isplitr
    · ipureintro; exact ⟨hbl, .start, rfl⟩
    isplitr
    · ipureintro; intro it lid hl; rw [pendItems_mvccStart] at hl; cases hl
    simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  first | rw [mvcc.api.pendItems_mvccStart] | rw [show mvcc.pendItems [[], []] [] = ∅ from mvcc.api.pendItems_mvccStart]
  (try wp_auto)
  rw [etcdStorage_val]
  (try wp_auto)
  -- `be.SetTxPostLockInsideApplyHook(func() { … })`
  wp_apply (wp_SetHook γB (rcP bc.BatchLimit') (mvccW gx) iprop(True) b (1 : Qp).half func.nil _)
    $$ [Hoh Hhk Hw1'] as ⟨Hoh, Hhk⟩
  · iframe Hisb Hoh Hhk Hw1'
  imod backend.plHook_persist γB _ $$ Hhk with #Hro
  ihave ⟨%f, #Hro, %Hfn, #Hhok⟩ : ∃ f : GoFunc, backend.plHookRO (GF := GF) γB f ∗ ⌜f ≠ func.nil⌝ ∗
      □ (∀ wv : writer, ⌜wv.applying' = applying_ptr ∧ wv.saved' = saved_ptr⌝ -∗ hookOk wv f) $$ [Hro]
  · iexists _
    iframe Hro
    isplitr
    · ipureintro; intro h; cases h
    iintro !> %wv %Hwv
    obtain ⟨h1, h2⟩ := Hwv
    iunfold hookOk
    iintro !> %i %s
    unfold mvcc.api.hookRun
    split
    · exfalso; rename_i h; cases h
    iintro !> !> %Φ' ⟨-, Hpre⟩ HΦ'
    iunfold hookPre at Hpre
    icases Hpre with ⟨Ha, Hs, %Hsi⟩
    rw [h1, h2, ← recv_eq_func_mk]
    wp_auto
    wp_apply_core sync.atomic.Int64.wp_Load applying_ptr (DFrac.own 1) $$ [] [-]
    · iPkgInit
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
    iintro Hcl
    inext
    iexists i
    iframe Ha
    iintro Ha
    imod Hcl with -
    imodintro
    wp_auto
    wp_apply_core sync.atomic.Int64.wp_Load saved_ptr (DFrac.own 1) $$ [] [-]
    · iPkgInit
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
    iintro Hcl
    inext
    iexists s
    iframe Hs
    iintro Hs
    imod Hcl with -
    imodintro
    wp_auto
    wp_if_destruct
    · wp_apply_core sync.atomic.Int64.wp_Store saved_ptr i $$ [] [-]
      · iPkgInit
      iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
      iintro Hcl
      inext
      iexists s
      iframe Hs
      iintro Hs
      imod Hcl with -
      imodintro
      (try wp_auto)
      iapply HΦ'
      iunfold hookPost
      rw [h1, h2]
      iframe
    · (try wp_auto)
      have : s = i := by word
      subst this
      iapply HΦ'
      iunfold hookPost
      rw [h1, h2]
      iframe
  -- `check(kv.Rev() == 1, …)`
  obtain ⟨⟨-, -, hRev, -, -, -, -, -, -, -, -, hKClose⟩, hNWS⟩ := hsh.2.1 wsl
  -- the store's reader tokens: the writer's, the registrar's, each reader's (`Readers + 2 ≤ 2 ^ 28`)
  have hRdN : 2 + sint.nat cfg.Readers' ≤ mvccReaderN := by
    rw [mvccReaderN_eq, backend.rdStockN_val]
    have : sint.nat cfg.Readers' = (sint.Z cfg.Readers').toNat := rfl
    omega
  rw [show mvccReaderN = 1 + (1 + (sint.nat cfg.Readers' + (mvccReaderN - (2 + sint.nat cfg.Readers'))))
    by omega]
  icases (hRdSplit γk 1 _).1 $$ Hrdrs with ⟨HkW, Hrdrs⟩
  icases (hRdSplit γk 1 _).1 $$ Hrdrs with ⟨HkR, Hrdrs⟩
  icases (hRdSplit γk _ _).1 $$ Hrdrs with ⟨HkRs, HkRest⟩
  wp_apply (hRev γk (fun σ => iprop(⌜σ = mvccStart⌝ ∗ mvccState γk σ))) $$ [HkW Hσ]
    as %rv ⟨HkW, %σ0, ⟨%Hσ0, Hσ⟩, %Hrv⟩
  · iframe Hkv HkW
    iauintro
    unfold atomic_acc
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑mvccN from Std.LawfulSet.empty_subset)
    iintro Hclose
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists mvccStart
    iframe Hσ
    isplit
    · iintro Hσ; imod Hclose with -; imodintro; iframe
    · iintro Hσ; imod Hclose with -; imodintro; iframe; ipureintro; rfl
  subst Hσ0 Hrv
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; rfl
  (try wp_auto)
  -- `newHistory()`
  wp_apply wp_newHistory as %hl ⟨%γh, Hmu, Hhr, Hhw, Habove, Hpub⟩
  (try wp_auto)
  -- the writer's struct: its map, its ticks channel
  wp_apply (wp_map_make1 (K := w64) (V := Bool)) as %lm Hlm
  (try wp_auto)
  wp_apply (chan.wp_make2 (V := w64) cfg.Watchers') as %ch %γch ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; exact ⟨hw0, hw⟩
  (try wp_auto)
  irename «$r0» => Hwr
  generalize «$r0_ptr» = w at *
  -- `kv.NewWatchStream()`
  wp_apply (hNWS γk) $$ [] as %wsv ⟨%ι, #Hws, HS, Hrcv⟩
  · iframe Hkv
  (try wp_auto)
  -- the watch check's struct
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %wm Hwm
  (try wp_auto)
  irename «$r0» => Hc
  generalize «$r0_ptr» = c at *
  iStructNamedSuffix Hc "C"
  -- the tester's ghost state: the world, the history's lock and handles, `c.mu`
  imod world_alloc hl γk ι γh $$ [Hσ HS Hpub Hhw]
    with ⟨%γ, %Hγ, #Hinv, Hidle, Hcl, Hreg, Hrcv1, Hrcv2, #Hlb0⟩
  · iframe Hσ HS Hpub Hhw
  obtain ⟨hγk, hγws, hγh⟩ := Hγ
  subst hγk hγws hγh
  have hrd2 : sint.nat cfg.Readers' + 2 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
    rw [sync.rwmutex.actualMaxReaders_unseal]
    have : sint.nat cfg.Readers' = (sint.Z cfg.Readers').toNat := rfl
    omega
  imod hist_alloc hl γ.h (sint.nat cfg.Readers' + 2) hrd2 $$ [Hmu Hhr Habove] with ⟨#Hhist, Hrds⟩
  · iframe Hmu Hhr Habove
  imod cmu_alloc c γ wm $$ [muC Hwm Hreg Hrcv1] with #Hcmu
  · iframe muC Hwm Hreg Hrcv1 Hlb0
  ipersist hC
  ipersist watchersC
  haveI : Persistent (wcCtx (GF := GF) c γ hl wm) := by unfold wcCtx; infer_instance
  ihave #Hwc : wcCtx (GF := GF) c γ hl wm $$ []
  · iunfold wcCtx
    iframe Hpkg Hinv Hhist Hcmu hC watchersC
    isplitr
    · iPkgInit
    iexists wsv, _
    iframe Hws Hkv
  -- the history's handles: the receiver's, the writer's, the readers'
  rw [show sint.nat cfg.Readers' + 2 = 1 + (1 + sint.nat cfg.Readers') by omega]
  icases (backend.bigSepL_replicate_add _ 1 (1 + sint.nat cfg.Readers')).1 $$ Hrds with ⟨Hrdr, Hrds⟩
  icases (backend.bigSepL_replicate_add _ 1 (sint.nat cfg.Readers')).1 $$ Hrds with ⟨Hrdw, Hrds⟩
  rw [List.replicate_one]
  ihave Hrdr := (BigSepL.bigSepL_singleton (PROP := IProp GF)).1 $$ Hrdr
  ihave Hrdw := (BigSepL.bigSepL_singleton (PROP := IProp GF)).1 $$ Hrdw
  -- the cells the goroutines read (never written again)
  ipersist ws
  ipersist c
  ipersist kv
  ipersist h
  iStructNamedSuffix cfg "F"
  ipersist PathF
  ipersist SeedF
  ipersist OpsF
  ipersist ReadersF
  ipersist ReadsF
  ipersist WatchersF
  ipersist DrainF
  ipersist w
  ihave %Hwsh := (hsh.2.2.2 wsv γ.kv γ.ws) $$ Hws
  obtain ⟨tyW, vW, hwsv, hWatch, hChan, -, -, -, hClose, -⟩ := Hwsh
  subst hwsv
  ihave ⟨#HisCh, #HrAu, -⟩ := hrecv _ _ _ $$ Hws
  -- `recvDone.Add(1)`, the receiver's goroutine
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") recvDone_ptr $$ recvDone with ⟨%γrd, Hrdwg⟩
  imod sync.join.init recvDone_ptr γrd $$ Hrdwg with Hrdwg
  wp_apply (sync.join.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add
    iprop(∃ ne : w64, cF go!"events" c ↦ ne) recvDone_ptr _ (W32 0)) $$ [Hrdwg] as ⟨Hrdwg, Hrdone⟩
  · iframe; ipureintro; decide
  (try wp_auto)
  wp_apply wp_fork_tok_body $$ [Hrdone Hrdr Hrcv Hrcv2 eventsC]
  · iintro Htt
    wp_auto
    wp_apply (hChan γ.kv γ.ws) $$ [] as %rch %Hrch
    · iframe Hws
    subst Hrch
    (try wp_auto)
    ihave IH : (∃ (rs : List WResp) (ne : w64) (rv : go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse),
        "resp" ∷ resp_ptr ↦ rv ∗ "Hrcv" ∷ wsRecv γ.ws rs ∗ "Hrcv2" ∷ ghostVar γ.rcv (1 : Qp).half rs ∗
        "Hev" ∷ cF go!"events" c ↦ ne ∗ "Hrdr" ∷ histRd hl γ.h ∗ "Htt" ∷ threadTok : IProp GF)
      $$ [resp Hrcv Hrcv2 eventsC Hrdr Htt]
    · iexists [], W64 0, _
      iframe
    wp_for IH
    wp_bind (App (Val (chan.receive _)) (Val _))
    iapply (chan.wp_receive (V := go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse)
      (wsChanOf γ.ws) (wsChanNames γ.ws)) $$ HisCh
    iintro -
    iapply HrAu $$ Hrcv
    iintro %v %ok Hv
    cases ok
    · -- the stream's channel closed: the loop's end, `recvDone.Done()`
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_for_post
      (try wp_auto)
      wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done
        iprop(∃ ne : w64, cF go!"events" c ↦ ne) recvDone_ptr) $$ [Hrdone Hev]
      · iframe Hrdone; iexists ne; iexact Hev
      (try wp_auto)
      iframe Htt
    · simp only [↓reduceIte]
      icases Hv with ⟨%r, Hrcv, Hwr⟩
      wp_auto
      wp_apply (wp_receive c γ hl wm rs r v ne) $$ [Hrdr Hrcv Hwr Hrcv2 Hev]
        as ⟨Hrdr, Hrcv, Hrcv2, Hev⟩
      · iframe Hwc Hrdr Hrcv Hwr Hrcv2 Hev
      wp_for_post
      iframe Hrdone
      iexists rs ++ [r], _, v
      iframe
  (try wp_auto)
  -- `wg.Add(2 + cfg.Readers)`: the writer's (its history handle back), the registrar's (its half
  -- of `γ.cl` back), the readers'
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr $$ wg with ⟨%γwg, Hwg⟩
  imod sync.join.init wg_ptr γwg $$ Hwg with Hwg
  have hlen : ([iprop(histRd (GF := GF) hl γ.h ∗ mvccReaders γ.kv 1 ∗
        mvccBackend γ.kv 1 (etcdStorage (rcKB γB b gx bc.BatchLimit')) iprop(True) ∗
        apply.bkRT (rcKB γB b gx bc.BatchLimit')),
      iprop(ghostVar γ.cl (1 : Qp).half false ∗ mvccReaders γ.kv 1)] ++
      List.replicate (sint.nat cfg.Readers') (mvccReaders (GF := GF) γ.kv 1)).length = 2 + sint.nat cfg.Readers' := by
    simp; omega
  rw [show W64 2 + cfg.Readers' = W64 (((2 + sint.nat cfg.Readers' : Nat) : Int)) by word]
  rw [← hlen]
  wp_apply (wp_Add_many sync.WaitGroup.wp_Add wg_ptr iprop(True)
      ([iprop(histRd (GF := GF) hl γ.h ∗ mvccReaders γ.kv 1 ∗
          mvccBackend γ.kv 1 (etcdStorage (rcKB γB b gx bc.BatchLimit')) iprop(True) ∗
          apply.bkRT (rcKB γB b gx bc.BatchLimit')),
        iprop(ghostVar γ.cl (1 : Qp).half false ∗ mvccReaders γ.kv 1)] ++
        List.replicate (sint.nat cfg.Readers') (mvccReaders (GF := GF) γ.kv 1))
      (by rw [hlen]; have : sint.nat cfg.Readers' = (sint.Z cfg.Readers').toNat := rfl; omega)) $$ [Hwg]
    as ⟨Hwg, Hdones⟩
  · iframe Hwg
  icases BigSepL.bigSepL_append.1 $$ Hdones with ⟨Hd2, Hdones⟩
  icases BigSepL.bigSepL_cons.1 $$ Hd2 with ⟨Hdw, Hd2⟩
  icases BigSepL.bigSepL_cons.1 $$ Hd2 with ⟨Hdr, -⟩
  (try wp_auto)
  -- the writer's struct, its counters, its ticks channel
  iStructNamedSuffix Hwr "W"
  ipersist kvW
  ipersist leW
  ipersist hW
  ipersist rW
  ipersist leasesW
  ipersist applyingW
  ipersist savedW
  ipersist ticksW
  ihave Happ : sync.atomic.ownInt64 (GF := GF) applying_ptr (DFrac.own 1) (W64 0) $$ [applying]
  · rw [sync.atomic.ownInt64_unseal]
    unfold sync.atomic.ownInt64Def
    rw [show ({ «_#0'» := zero_val _, «_#1'» := zero_val _, v' := W64 0 } : sync.atomic.Int64) =
      zero_val _ from rfl]
    iexact applying
  ihave Hsav : sync.atomic.ownInt64 (GF := GF) saved_ptr (DFrac.own 1) (W64 0) $$ [saved]
  · rw [sync.atomic.ownInt64_unseal]
    unfold sync.atomic.ownInt64Def
    rw [show ({ «_#0'» := zero_val _, «_#1'» := zero_val _, v' := W64 0 } : sync.atomic.Int64) =
      zero_val _ from rfl]
    iexact saved
  ihave Hoc' : (ownChan γch w64 ChanState.Idle ∨ ownChan γch w64 (ChanState.Buffered ([] : List w64)) :
      IProp GF) $$ [Hoc]
  · by_cases hz : cfg.Watchers' = W64 0
    · rw [ite_eq_left hz]; ileft; iexact Hoc
    · rw [ite_eq_right hz]; iright; iexact Hoc
  imod start_spsc ch (tickP (GF := GF) γ) (fun _ => iprop(True)) γch $$ Hch Hoc'
    with ⟨%γt, #Hspsc, Hprod, Hcons⟩
  subst Hγl
  let wv : writer :=
    { kv' := interface.mkOk go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty.PointerType #wsl,
      le' := lease.lessorIface lp, h' := hl, r' := «$v3_ptr», leases' := lm, nextID' := W64 0,
      vals' := W64 0, applying' := applying_ptr, saved' := saved_ptr, ticks' := ch }
  ihave #Hwro : writerRO (GF := GF) w wv $$ []
  · iunfold writerRO; iframe kvW leW hW rW leasesW applyingW savedW ticksW
  haveI : Persistent (writerCtx (GF := GF) w wv γ (etcdStorage (rcKB γB b gx bc.BatchLimit')) f) := by
    unfold writerCtx hookOk; infer_instance
  ihave #Hctx : writerCtx (GF := GF) w wv γ (etcdStorage (rcKB γB b gx bc.BatchLimit')) f $$ []
  · iunfold writerCtx
    iframe Hpkg Hwro Hinv Hhist Hkv
    isplitr
    · iPkgInit
    isplitr
    · iPkgInit
    isplitr
    · rw [etcdStorage_hookIs, rcKB_γB]; iexact Hro
    iapply Hhok
    ipureintro; exact ⟨rfl, rfl⟩
  -- the writer's goroutine: `w.run(cfg.Ops); wg.Done()`
  wp_apply wp_fork_tok_body $$ [Hdw Hrdw Hidle Hmb «$v3» Hlm Hlown Hrvk Hever Hlrd2 Hrt Hor Hbeon
      Hwops Hrdo Hdel Hrbo nextIDW valsW Happ Hsav Hprod HkW]
  · iintro Htt
    wp_auto
    ihave Hle := writerLe_start w wv γ γB b gx bc.BatchLimit' f lp rd (sint.nat cfg.Ops') _ rfl Hfn
      $$ [Hlrd2 Hrvk Hever Hrt Hor Hbeon Hwops Hrdo Hdel Hrbo nextIDW]
    · iframe Hlinv Hmode Hlcfg Hguard Happly Hisb Hro Hlrd2 Hrvk Hever Hrt Hor Hbeon Hwops Hrdo Hdel
        Hrbo nextIDW
      iPkgInit
    ihave Hown : writerOwn (GF := GF) wv γ (etcdStorage (rcKB γB b gx bc.BatchLimit')) 1 mvccStart hist0
        [] $$ [HkW Hmb Hrdw Hidle «$v3» Hlm Hlown]
    · iunfold writerOwn
      iframe HkW Hmb Hrdw Hidle
      isplitl [«$v3»]
      · iexists _; iexact «$v3»
      isplitl [Hlm]
      · iexists ∅; iframe Hlm; ipureintro; intro id; simp
      rw [pendItems_start]; iexact Hlown
    have hOpsN : sint.Z cfg.Ops' ≤ (sint.nat cfg.Ops' : Int) := by
      have : sint.nat cfg.Ops' = (sint.Z cfg.Ops').toNat := rfl
      omega
    wp_apply (wp_run w wv γ (rcKB γB b gx bc.BatchLimit') f 1 mvccStart hist0 [] (0 : w64)
        (sint.nat cfg.Ops') (backend.wbTok γB)
        (apply.bkRT (rcKB γB b gx bc.BatchLimit')) (W64 0) (0 : w64)
        cfg.Ops' γt hops0 (by omega) hOpsN (by decide) (by word) (by word))
      $$ [Hown Hle Happ Hsav valsW Hprod] as Hrun
    · iframe Hctx Hown Hle valsW
      isplitl [Happ Hsav]
      · iunfold hookPre; iframe Happ Hsav; ipureintro; decide
      iunfold ticksW
      iunfold isTicks
      iframe Hspsc
      iexists []; iexact Hprod
    (try wp_auto)
    iunfold runSt at Hrun
    icases Hrun with ⟨%σ1, %Hs1, %L1, %n1, %k1, %s1, %v1, Hown, Hle, -⟩
    iunfold writerOwn at Hown
    icases Hown with ⟨HkW, Hmb, Hrdw, -⟩
    iunfold writerLe at Hle
    icases Hle with ⟨%lp1, %rd1, %r1, %U1, -, -, -, -, HRT, -⟩
    wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done
      iprop(histRd (GF := GF) hl γ.h ∗ mvccReaders γ.kv 1 ∗
        mvccBackend γ.kv 1 (etcdStorage (rcKB γB b gx bc.BatchLimit')) iprop(True) ∗
        apply.bkRT (rcKB γB b gx bc.BatchLimit'))
      wg_ptr) $$ [Hdw Hrdw HkW Hmb HRT]
    · iframe Hdw Hrdw HkW Hmb HRT
    (try wp_auto)
    iframe Htt
  (try wp_auto)
  -- the registrar's goroutine: `c.register(ws, &rng{…}, w.ticks); wg.Done()`
  wp_apply wp_fork_tok_body $$ [Hdr Hcons Hcl HkR]
  · iintro Htt
    wp_auto
    wp_apply (wp_register c γ hl wm _ _ _ γt ch []) $$ [HkR «$a1» Hcons Hcl]
      as ⟨HkR, Hcl, -⟩
    · iframe Hwc Hws HkR «$a1» Hcons Hcl
      iunfold isTicks; iexact Hspsc
    (try wp_auto)
    wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done
      iprop(ghostVar (GF := GF) γ.cl (1 : Qp).half false ∗ mvccReaders γ.kv 1) wg_ptr) $$ [Hdr Hcl HkR]
    · iframe Hdr Hcl HkR
    (try wp_auto)
    iframe Htt
  (try wp_auto)
  -- the readers' goroutines
  have hRn : sint.nat cfg.Readers' = (sint.Z cfg.Readers').toNat := rfl
  ihave IH : (∃ (i : w64), "id" ∷ id_ptr ↦ i ∗
      "Hrds" ∷ ([∗list] _x ∈ List.replicate (sint.nat cfg.Readers' - sint.nat i) (), histRd hl γ.h) ∗
      "Hdones" ∷ ([∗list] Q ∈ List.replicate (sint.nat cfg.Readers' - sint.nat i)
        (mvccReaders (GF := GF) γ.kv 1), sync.join.ownDone wg_ptr Q) ∗
      "HkRs" ∷ mvccReaders γ.kv (sint.nat cfg.Readers' - sint.nat i) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z cfg.Readers'⌝ : IProp GF) $$ [id Hrds Hdones HkRs]
  · iexists W64 0
    rw [show sint.nat (W64 0) = 0 from rfl, Nat.sub_zero]
    iframe
    ipureintro; exact ⟨by decide, hrd0⟩
  wp_for IH
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z cfg.Readers' := by simpa using Hif
    have hin : sint.nat i = (sint.Z i).toNat := rfl
    rw [show sint.nat cfg.Readers' - sint.nat i =
      (sint.nat cfg.Readers' - (sint.nat i + 1)) + 1 by omega, List.replicate_succ, List.replicate_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hrds with ⟨Hrd, Hrds⟩
    icases BigSepL.bigSepL_cons.1 $$ Hdones with ⟨Hd, Hdones⟩
    icases (hRdSplit γ.kv (sint.nat cfg.Readers' - (sint.nat i + 1)) 1).1 $$ HkRs with ⟨HkRs, HkR1⟩
    (try wp_auto)
    ipersist r
    wp_apply wp_fork_tok_body $$ [Hd Hrd «$r0» HkR1]
    · iintro Htt
      wp_auto
      wp_apply (wp_reader _ hl _ γ _ _) $$ [Hrd HkR1 «$r0»] as ⟨Hrd, HkR1, -⟩
      · iframe Hkv Hinv Hrd HkR1 «$r0»
      (try wp_auto)
      wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done
        (mvccReaders (GF := GF) γ.kv 1) wg_ptr) $$ [Hd HkR1]
      · iframe Hd HkR1
      (try wp_auto)
      iframe Htt
    wp_for_post
    iframe
    iexists (i + W64 1)
    have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    rw [hi1]
    iframe
    ipureintro; constructor <;> word
  -- `wg.Wait()`: the writer's history handle, the registrar's half of `γ.cl`
  wp_apply (lc := 1) (sync.join.WaitGroup.wp_Wait_of sync.WaitGroup.wp_Wait _ _ wg_ptr) $$ [Hwg]
    as ⟨Hres, -⟩
  · iframe Hwg
  imod lc_fupd_elim_later $$ Hlc1 Hres with Hres
  icases Hres with ⟨-, Hres⟩
  icases BigSepL.bigSepL_append.1 $$ Hres with ⟨Hres, HkRds⟩
  icases BigSepL.bigSepL_cons.1 $$ Hres with ⟨⟨Hrdw, HkW, Hmb, HRT⟩, Hres⟩
  icases BigSepL.bigSepL_cons.1 $$ Hres with ⟨⟨Hcl, HkR⟩, -⟩
  (try wp_auto)
  -- `last := h.published.Load()`, in the history
  wp_apply_core sync.atomic.Int64.wp_Load (hPub hl) (DFrac.own 1) $$ [] [-]
  · iPkgInit
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑worldN from Std.LawfulSet.empty_subset)
  iintro Hcl2
  inext
  iunfold worldInv at Hi
  icases Hi with ⟨%σ, %S, %p, %Hl, %W, Hσ, Hgσ, HS, Hreg, Hpub, Hpv, Hpm, #Hlb, %Hok⟩
  ihave ⟨Hσ, %Hpf⟩ := pub_facts hreach σ p Hl _ γ.kv Hok.2.1 Hok.2.2.1 Hok.2.2.2.1 $$ [Hσ]
  · iframe Hkv Hσ
  iexists p
  iframe Hpub
  iintro Hpub
  imod Hcl2 with -
  imod Hclose $$ [Hσ Hgσ HS Hreg Hpub Hpv Hpm] with -
  · inext; iunfold worldInv; iexists σ, S, p, Hl, W; iframe; iframe #; ipureintro; exact Hok
  imodintro
  (try wp_auto)
  -- `complete := c.complete(last)`
  wp_apply (wp_complete c γ hl wm Hl p Hpf.1 Hpf.2) $$ [Hrdw] as %cmp Hrdw
  · iframe Hwc Hrdw Hlb
  (try wp_auto)
  -- the drain: `if cfg.Drain > 0 { … }` (what `complete` answers is only reported)
  ipersist last
  wp_join iprop(∃ cb : Bool, complete_ptr ↦ cb ∗ histRd hl γ.h) with [complete Hrdw]
    as ⟨%cb, complete, Hrdw⟩
  · wp_apply time.wp_Now as %t0 -
    wp_apply time.Time.wp_Add as %dl -
    (try wp_auto)
    ihave IH : (∃ (cb : Bool), "complete" ∷ complete_ptr ↦ cb ∗ "Hrdw" ∷ histRd hl γ.h : IProp GF)
      $$ [complete Hrdw]
    · iexists _; iframe
    wp_for IH
    cases cb
    · -- not complete: before the deadline, wait and ask again
      (try wp_auto)
      wp_apply time.wp_Now as %t1 -
      wp_apply time.Time.wp_Before as %bf -
      (try wp_auto)
      cases bf
      · (try wp_auto)
        simp only [val_bool_eq, _root_.decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
        isplitr
        · itrivial
        iexists false
        iframe
      · (try wp_auto)
        simp only [_root_.decide_true, ↓reduceIte]
        wp_apply time.wp_Sleep
        (try wp_auto)
        wp_apply (wp_complete c γ hl wm Hl p Hpf.1 Hpf.2) $$ [Hrdw] as %cmp' Hrdw
        · iframe Hwc Hrdw Hlb
        (try wp_auto)
        wp_for_post
        iframe
        iexists cmp'
        iframe
    · (try wp_auto)
      simp only [val_bool_eq, _root_.decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte]
      isplitr
      · itrivial
      iexists true
      iframe
  -- `ws.Close()`: the stream closed (the registrar's half of `γ.cl` back)
  wp_apply (hClose γ.kv γ.ws (fun _ => iprop(True))) $$ [Hcl] as -
  · iframe Hws
    iapply close_au hpers hl γ $$ [Hcl]
    iframe Hinv Hcl
  (try wp_auto)
  -- `recvDone.Wait()`: the receiver's `c.events` back
  wp_apply (sync.join.WaitGroup.wp_Wait_of sync.WaitGroup.wp_Wait _ _ recvDone_ptr) $$ [Hrdwg]
    as ⟨Hres, -⟩
  · iframe Hrdwg
  icases Hres with ⟨-, %ne, Hev⟩
  (try wp_auto)
  -- `check(kv.Close() == nil, …)`
  wp_apply (hKClose γ.kv) $$ [Hopn] as Hclosed
  · iframe Hkv Hopn
  -- the census: the backend's whole open token, every reader of it done (`stop_census_open`)
  rw [hlen]
  ihave HkAll := readers_gather hRdSplit γ.kv (sint.nat cfg.Readers')
    (mvccReaderN - (2 + sint.nat cfg.Readers')) $$ [HkRest HkRds]
  · iframe HkRest HkRds
  ihave HkAll := (hRdSplit γ.kv 1 _).2 $$ [HkR HkAll]
  · iframe HkR HkAll
  ihave HkAll := (hRdSplit γ.kv 1 _).2 $$ [HkW HkAll]
  · iframe HkW HkAll
  rw [show 1 + (1 + (sint.nat cfg.Readers' + (mvccReaderN - (2 + sint.nat cfg.Readers')))) =
    mvccReaderN by omega]
  iunfold apply.bkRT at HRT
  icases HRT with ⟨-, Hor⟩
  iunfold rcCensus at Hcen
  ispecialize Hcen $$ %γ.kv %(1 : Qp) Hor Hoh
  imod Hcen $$ [Hclosed HkAll Hmb] with ⟨Hone, -⟩
  · iframe Hclosed HkAll Hmb
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; rfl
  (try wp_auto)
  -- the report: `c.events`, `h.aboveFloor.Load()`
  ihave #Hhist' := Hhist
  iunfold isHistory at Hhist'
  icases Hhist' with ⟨-, #Habinv⟩
  wp_apply_core sync.atomic.Int64.wp_Load (hAbove hl) (DFrac.own 1) $$ [] [-]
  · iPkgInit
  iinv Habinv with Hi Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑histN from Std.LawfulSet.empty_subset)
  iintro Hcl2
  inext
  iunfold aboveInv at Hi
  icases Hi with ⟨%a, Ha⟩
  iexists a
  iframe Ha
  iintro Ha
  imod Hcl2 with -
  imod Hclose $$ [Ha] with -
  · inext; iunfold aboveInv; iexists a; iexact Ha
  imodintro
  (try wp_auto)
  iapply HΦ
  iframe Hstop Hisb Hsc Hone

end proof

end mvccrand
end EtcdGrove
end Perennial
