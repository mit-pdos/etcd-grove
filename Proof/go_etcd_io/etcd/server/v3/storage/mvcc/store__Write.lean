/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Write
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newMetricsTxnWrite

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.store.Write.wp_proof (hNew : mvcc.newMetricsTxnWrite.spec (GF := GF) (hG := hG)) :
    mvcc.store.Write.spec (GF := GF) (hG := hG) := by
  intro s γ trace P Pre Q f te clb Z
  wp_start as ⟨#Hs, Hrd, #HZ, #Hclb, Htok, Hwt, %Htrnn, #HhookC, Hpre, #Htriple, Htrc⟩
  ihave #Hs0 : mvcc.isStore s γ $$ []
  · iexact Hs
  iunfold mvcc.isStore at Hs
  icases Hs with ⟨%b, %le, %ti, %lg, %P0, %Dep, %scfg, %ssched, %sstop, %shs, Hs⟩
  iNamed Hs
  iunfold mvcc.storeReaderC at Hrd
  icases Hrd with ⟨%ti2, Hrd⟩
  iNamedSuffix Hrd "R"
  wp_auto_lc 1
  -- the caller's hook is the store's
  imod mvcc.hookP_agree_lc ⊤ γ P P0 f $$ [$Hlc1 $HhookC $Hhook] with ⟨#HPP0, #HP0P⟩
  ihave #HhookC' := HhookC
  iunfold mvcc.hookIs at HhookC'
  icases HhookC' with ⟨-, #Hhf⟩
  ihave #HhookW : mvcc.hookIs γ P0 f $$ []
  · iunfold mvcc.hookIs; iframe Hhook Hhf
  ihave #Htr0 : □ ({{ P0 ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) $$ []
  · iintro !> %Φ !> ⟨HP0, Hpre⟩ HΦ
    iapply Htriple $$ %Φ [HP0 Hpre] HΦ
    iframe Hpre
    iapply HP0P
    iexact HP0
  -- `s.mu.RLock()`: its part of `s.mu`'s resource, at the compaction revision `cm`, at or
  -- above the caller's lower bound
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HmuR] as ⟨Hmul, HmuP⟩
  wp_auto_lc 2
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.muInv s γ sync.rfrac)) $$ Hlc1 HmuP with HmuP
  iunfold mvcc.muInv at HmuP
  icases HmuP with ⟨%cm, HmuP, Hwr, Hfs⟩
  icases mvcc.fieldShare_open s γ _ b ti ssched sstop $$ [Hpin Hfs] with ⟨Hfb, Hfidx, Hfsch, Hfstop⟩
  · iframe Hpin Hfs
  iunfold mvcc.muInvAt at HmuP
  iNamed HmuP
  icases mvcc.crevUB_lb_keep γ.idx _ cm clb HcM $$ [$HcrevM $Hclb] with ⟨HcrevM, %Hclbc⟩
  icases mvcc.crevUB_get_lb γ.idx _ cm $$ HcrevM with ⟨HcrevM, #Hlbc⟩
  ihave #HclM0 := HclM
  -- `tx := s.b.BatchTx()`
  iunfold mvcc.isKeyBackendG at Hbk
  icases Hbk with ⟨%bi, %Hbi, #HC, #HR, #HB, -⟩
  subst Hbi
  (try wp_auto)
  wp_apply HB as %bt #Hbt
  (try wp_auto)
  ihave Hfs := mvcc.fieldShare_close s γ _ _ ti ssched sstop $$ [Hpin Hfb Hfidx Hfsch Hfstop]
  · iframe Hpin Hfb Hfidx Hfsch Hfstop
  ihave Hmuh : mvcc.muHeld s γ cm $$ [Hmul HcmpM HcrevM Hfs]
  · iunfold mvcc.muHeld
    iframe Hmul Hfs
    iunfold mvcc.muInvAt
    iframe HcmpM HcrevM
    iframe #
    ipureintro; exact HcM
  iunfold mvcc.isBatchTxG at Hbt
  icases Hbt with ⟨%Locked, %LockedO, #Hbt, -⟩
  ihave #Hbt0 : mvcc.batchTxSpecG bt (mvcc.bucketView γ) (mvcc.storeRT γ) (mvcc.storeWT γ)
      (mvcc.storePutOk γ) (mvcc.delKey γ) (mvcc.storeW s γ) Dep (mvcc.storeCmp γ) Locked P0 (mvcc.hookFn γ) $$ []
  · iexact Hbt
  iunfold mvcc.batchTxSpecG at Hbt
  icases Hbt with ⟨#HLock, -, -, -, -⟩
  -- `tx.LockInsideApply()`: the writer's resources, the hook run on the caller's `Pre`
  ihave #HLock' := HLock $$ %Pre %Q %f
  wp_apply HLock' $$ [$Hpre $Htr0 $HrtR $Hwt $Hhf] as ⟨Hlocked, HW, HQ, HrtR⟩
  (try wp_auto)
  ihave HW := mvcc.storeW_get s γ $$ [$Hreg $HW]
  iunfold mvcc.writerRes at HW
  icases HW with ⟨%L, Hwk, HwvW, Hbv, #HcertW, %HneW, Hcres⟩
  -- the writer's state, checked out of the writer's invariant (D22 receiver epochs, S2): the
  -- batch lock's key and the transaction's part of `s.mu`'s deposit ghost deposited
  ihave Hwr : mvcc.wDep γ $$ [Hwr]
  · iunfold mvcc.wDep; iexact Hwr
  imod mvcc.writerInv_checkout s γ $$ Hlc2 Hwi Hwk Hwr with HL
  iunfold mvcc.writerL at HL
  icases HL with ⟨%ilog, %ntok, HL⟩
  iNamed HL
  icases mvcc.ghostVar_join_halves γ.wv ilog L $$ [Hwv HwvW] with ⟨Hwv, %HL⟩
  · iframe Hwv HwvW
  subst HL
  -- the compaction revision is a revision of the committed log (`s.mu`'s certified log is below
  -- the writer's)
  iunfold mvcc.crevSafe at HclM0
  icases HclM0 with ⟨%log₀, #Hc0, %Hl0⟩
  ihave %Hpre0 := mvcc.idxWriter_cert_prefix γ.idx ilog [] log₀ $$ [Hw Hc0]
  · iframe Hw; iexact Hc0
  (try wp_auto)
  -- `make([]*mvccpb.KeyValue, 0, 4)`
  wp_apply (wp_slice_make3 (V := Loc) (W64 0) (W64 4) (by decide)) as %chs ⟨Hchs, Hcap, -⟩
  (try wp_auto)
  wp_apply (hNew _) as %mw Hmw
  (try wp_auto)
  iapply HΦ
  iframe HQ
  iexists ilog, cm
  iframe Hlbc
  isplitl
  rotate_left
  · ipureintro; exact Hclbc
  iunfold mvcc.isTxnWrite
  iexists «$r0_ptr», W64 0
  iframe Hmw
  isplitr [Htrc]
  rotate_left
  · iexists te; iexact Htrc
  iunfold mvcc.storeTxnWriteIs
  iexists ti2, bt, Locked, chs, [], ntok, P0, f, Dep
  simp only [named, mvcc.pendPuts_nil]
  simp only [List.replicate_zero]
  iframe Htoks Htok «$r0» Hchs Hcap Hlocked Hw Hclog Hcur Hbv Hwv Hmuh HrevMuR HtiR HrtR Hcres Hlrd
  iframe #
  isplitl []
  · ipureintro; exact Hbudget
  isplitl []
  · ipureintro; rfl
  isplitl []
  · iunfold mvcc.changesAre
    iapply BigSepL.bigSepL_nil_intro
    iempintro
  ipureintro; exact ⟨Hne, Htrnn, HcM, by have := Hpre0.length_le; omega⟩

end proof

end EtcdGrove
end Perennial
