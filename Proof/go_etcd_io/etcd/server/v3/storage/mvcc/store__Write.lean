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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.store.Write.wp_proof (hNew : mvcc.newMetricsTxnWrite.spec (GF := GF) (hG := hG)) :
    mvcc.store.Write.spec (GF := GF) (hG := hG) := by
  intro s γ trace P Pre Q f te clb Z
  wp_start as ⟨#Hs, Hrd, #HZ, #Hclb, Htok, Hwt, %Htrnn, HhookC, Hpre, #Htriple, Htrc⟩
  -- the caller's hook: its facts and the writer's fragment (D22 receiver epochs, S5b: the caller's
  -- names are the current ones)
  icases (mvcc.hookIs_split γ P f).1 $$ HhookC with ⟨#HhookC, Hfrag⟩
  iunfold mvcc.writerFrag at Hfrag
  icases Hfrag with ⟨%ow, Hpinw⟩
  ihave #Hs0 : mvcc.isStore s γ $$ []
  · iexact Hs
  iunfold mvcc.isStore at Hs
  iNamed Hs
  iunfold mvcc.storeReaderC at Hrd
  iNamedSuffix Hrd "R"
  wp_auto_lc 1
  ihave Hlc0 := Hlc1
  -- `s.mu.RLock()`: its part of `s.mu`'s resource, at the compaction revision `cm`, at or
  -- above the caller's lower bound
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HmuR] as ⟨Hmul, HmuP⟩
  wp_auto_lc 3
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.muInv s γ sync.rfrac)) $$ Hlc1 HmuP with HmuP
  iunfold mvcc.muInv at HmuP
  icases HmuP with ⟨%cm, HmuP, Hwr, Hfs⟩
  -- the share of the fields at the writer's names (its fragment pins them; S5b)
  icases mvcc.fieldShare_pin s γ _ _ ow $$ [Hpinw Hfs] with ⟨Hpinw, Hfs⟩
  · iframe Hpinw Hfs
  iunfold mvcc.fieldShareAt at Hfs
  iNamed Hfs
  ihave #Hph0 := Hph
  iunfold mvcc.physOk at Hph0
  iNamed Hph0
  -- the caller's hook is the store's
  imod mvcc.hookP_agree_lc ⊤ γ P Ph f $$ [$Hlc0 $HhookC $Hhook] with ⟨#HPP0, #HP0P⟩
  ihave #HhookC' := HhookC
  iunfold mvcc.hookOk at HhookC'
  icases HhookC' with ⟨-, #Hhf⟩
  ihave #HhookW : mvcc.hookOk γ Ph f $$ []
  · iunfold mvcc.hookOk; iframe Hhook Hhf
  ihave #Htr0 : □ ({{ Ph ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) $$ []
  · iintro !> %Φ !> ⟨HP0, Hpre⟩ HΦ
    iapply Htriple $$ %Φ [HP0 Hpre] HΦ
    iframe Hpre
    iapply HP0P
    iexact HP0
  -- a slot of the index's lock, out of the readers' pool (D22 receiver epochs, S4)
  icases (mvcc.wDep_halves γ).1 $$ Hwr with ⟨Hwr, Hwr2⟩
  imod mvcc.readerPool_checkout γ _ ow $$ Hlc3 Hpool Hpinw HtkR Hwr2 with ⟨Hslot, Htko, Hpinw⟩
  iunfold mvcc.idxSlot at Hslot
  icases Hslot with ⟨HtiR, HrtR⟩
  iunfold mvcc.storeFields at Hflds
  iNamed Hflds
  iunfold mvcc.muInvAt at HmuP
  iNamed HmuP
  icases mvcc.crevUB_lb_keep γ.idx _ cm clb HcM $$ [$HcrevM $Hclb] with ⟨HcrevM, %Hclbc⟩
  icases mvcc.crevUB_get_lb γ.idx _ cm $$ HcrevM with ⟨HcrevM, #Hlbc⟩
  ihave #HclM0 := HclM
  -- `tx := s.b.BatchTx()`
  ihave #Hbk0 := Hbk
  iunfold mvcc.isKeyBackendG at Hbk
  icases Hbk with ⟨%bi, %Hbi, #HC, #HR, #HB, -⟩
  rw [Hbi]
  (try wp_auto)
  wp_apply HB as %bt #Hbt
  (try wp_auto)
  ihave Hfs : mvcc.fieldShareAt s γ sync.rfrac.half ow $$ [Hcur Hfb Hfidx Hfsch Hfstop Hfrst]
  · iunfold mvcc.fieldShareAt
    simp only [named]
    iframe Hcur Hfrst Hph
    iunfold mvcc.storeFields; simp only [named]; rw [Hbi]; iframe Hfb Hfidx Hfsch Hfstop
  ihave Hmuh : mvcc.muHeld s γ cm ow.ti $$ [Hmul HcmpM HcrevM Hfs]
  · iunfold mvcc.muHeld
    iframe Hmul
    isplitr [Hfs]
    · iunfold mvcc.muInvAt
      iframe HcmpM HcrevM
      iframe #
      ipureintro; exact HcM
    iexists ow
    iframe Hfs
    ipureintro; rfl
  iunfold mvcc.isBatchTxG at Hbt
  icases Hbt with ⟨%Locked, %LockedO, #Hbt, -, #HbtB⟩
  ihave #Hbt0 : mvcc.batchTxSpecG bt (mvcc.bucketView γ) (mvcc.storeRT γ) (mvcc.storeWT γ)
      (mvcc.storePutOk γ) (mvcc.delKey γ) (mvcc.storeW s γ) Dep (mvcc.storeCmp γ) Locked Ph (mvcc.hookFn γ) (mvcc.storeRb γ)
      (mvcc.kbMW γ.kb) $$ []
  · iexact Hbt
  iunfold mvcc.batchTxSpecG at Hbt
  icases Hbt with ⟨#HLock, -, -, -, -⟩
  -- `tx.LockInsideApply()`: the writer's resources, the hook run on the caller's `Pre`
  ihave #HLock' := HLock $$ %Pre %Q %f
  wp_apply HLock' $$ [$Hpre $Htr0 $HrtR $Hwt $Hhf] as ⟨Hlocked, HW, HQ, HrtR⟩
  (try wp_auto)
  -- the writer's state, checked out of the writer's invariant (D22 receiver epochs, S2): the
  -- batch lock's key and the transaction's part of `s.mu`'s deposit ghost deposited; the store
  -- registered in its backend (S6: now, if a restore left it pending)
  imod mvcc.writerInv_checkout s γ _ ow $$ Hlc2 Hwi Hpinw HW Hwr
    with ⟨HL, #Hreg, ⟨%L, HwvW, Hbv, #HcertW, %HneW, Hcres⟩, Hpinw⟩
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
  isplitr [Hpinw]
  rotate_left
  · iunfold mvcc.hookIs; iframe HhookC; iunfold mvcc.writerFrag; iexists ow; iexact Hpinw
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
  iexists ow.ti, bt, Locked, chs, [], ntok, Ph, f, Dep
  simp only [named, mvcc.pendPuts_nil]
  simp only [List.replicate_zero]
  iframe Htoks Htok «$r0» Hchs Hcap Hlocked Hw Hclog Hcur Hbv Hwv Htko Hmuh HrevMuR HtiR HrtR Hcres Hlrd
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
