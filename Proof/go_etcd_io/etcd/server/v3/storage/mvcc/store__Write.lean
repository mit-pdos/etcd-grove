/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.CmpSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnSteps
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
  intro s γ trace P Pre Q hk dq te clb Z logP qf ow G F
  wp_start as ⟨#Hs, Hrd, #HZ, #Hclb, Htok, Hwt, %Htrnn, Hctx, Hpinw, HG, #HFG, Hwcb, HpinP, Htrc⟩
  -- the writer's pin: its quarter of the view, joined below with `writerRes`'s, and its loan
  iunfold mvcc.writerPin at HpinP
  icases HpinP with ⟨HbvP, Hloan⟩
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
  -- the share of the fields at the caller's names (its share of the current objects pins them)
  icases mvcc.fieldShare_pin s γ _ _ ow $$ [Hpinw Hfs] with ⟨Hpinw, Hfs⟩
  · iframe Hpinw Hfs
  iunfold mvcc.fieldShareAt at Hfs
  iNamed Hfs
  ihave #Hph0 := Hph
  iunfold mvcc.physOk at Hph0
  iNamed Hph0
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
  ihave Hmuh : mvcc.muHeld s γ cm ow.ti $$ [Hmul HcmpM HcrevM HwcM Hfs]
  · iunfold mvcc.muHeld
    iframe Hmul
    isplitr [Hfs]
    · iunfold mvcc.muInvAt
      iframe HcmpM HcrevM HwcM
      iframe #
      ipureintro; exact HcM
    iexists ow
    iframe Hfs
    ipureintro; rfl
  iunfold mvcc.isBatchTxG at Hbt
  icases Hbt with ⟨%Locked, %LockedO, #HbtF, -, #HbtB⟩
  ihave #Hbt := mvcc.batchTxSpecG_noNil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ $$ HbtF
  ihave #Hbt0 : mvcc.batchTxSpecG bt (mvcc.bucketView γ) (mvcc.storeRT γ) (mvcc.storeWT γ)
      (mvcc.storePutOk γ) (mvcc.delKey γ) (mvcc.storeW s γ) Dep (mvcc.storeCmp γ) Locked Ph (mvcc.hookFn γ) (mvcc.storeRb γ)
      (mvcc.kbMWv γ.kb γ.bucket) $$ []
  · iexact Hbt
  iunfold mvcc.batchTxSpecG at Hbt
  icases Hbt with ⟨#HLock, -, -, -, -⟩
  -- `tx.LockInsideApply()`, by the hook's state (request 4): set, the hook run on the caller's
  -- `Pre` (its invariant the store's); unset, the nil arm (`lockNilSpec`, the share `dq` of the hook
  -- at `nil` lent) and the caller's view shift from the lock's invariant and `Pre`
  wp_bind (App (Val #(methods bt.ty go!"LockInsideApply" bt.v)) (Val #()))
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ Locked [] ∗ mvcc.storeW s γ ∗ (|={⊤}=> Q) ∗
      mvcc.storeRT γ ∗ mvcc.lockBackM γ P hk dq))) $$ [Hctx HrtR Hwt Hlc0]
  · cases hk with
    | some f =>
      rw [mvcc.writeCtxM_some, mvcc.lockBackM_some]
      icases Hctx with ⟨#HhookC, Hpre, #Htriple⟩
      -- the caller's hook is the store's
      imod mvcc.hookP_agree_lc ⊤ γ P Ph f $$ [$Hlc0 $HhookC $Hhook] with ⟨#HPP0, #HP0P⟩
      ihave #HhookC' := HhookC
      iunfold mvcc.hookOk at HhookC'
      icases HhookC' with ⟨-, #Hhf⟩
      ihave #Htr0 : □ ({{ Ph ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) $$ []
      · iintro !> %Φ !> ⟨HP0, Hpre⟩ HΦ
        iapply Htriple $$ %Φ [HP0 Hpre] HΦ
        iframe Hpre
        iapply HP0P
        iexact HP0
      ihave #HLock' := HLock $$ %Pre %Q %f
      iapply HLock' $$ [$Hpre $Htr0 $HrtR $Hwt $Hhf]
      inext
      iintro ⟨Hlocked, HW, HQ, HrtR⟩
      iframe Hlocked HW HrtR HhookC
      isplitr
      · ipureintro; rfl
      imodintro; iexact HQ
    | none =>
      rw [mvcc.writeCtxM_none, mvcc.lockBackM_none]
      icases Hctx with ⟨#HhP, Hnil, Hpre, Hupd⟩
      -- the caller's invariant is the store's
      imod mvcc.hookP_agree_lc2 ⊤ γ P Ph $$ [$Hlc0 $HhP $Hhook] with ⟨#HPP0, #HP0P⟩
      ihave #HbtF' := HbtF
      iunfold mvcc.batchTxSpecG at HbtF'
      icases HbtF' with ⟨-, -, -, -, -, -, -, -, -, #HLN⟩
      ispecialize HLN $$ %dq
      iunfold mvcc.lockNilSpec at HLN
      ihave #HLN' := HLN $$ %Pre
      iapply HLN' $$ [$Hpre $HrtR $Hwt $Hnil]
      inext
      iintro ⟨Hlocked, HW, HP0, Hpre, HrtR, Hnil⟩
      ihave HP := HP0P $$ HP0
      ihave HQ : iprop(|={⊤}=> Q) $$ [Hupd HP Hpre]
      · iapply Hupd; iframe HP Hpre
      iframe Hlocked HW HQ HrtR HhP Hnil
      ipureintro; rfl
  iintro %v ⟨%Hv, Hlocked, HW, HQ, HrtR, Hback⟩
  subst Hv
  imod HQ with HQ
  (try wp_auto)
  -- the writer's state, checked out of the writer's invariant (D22 receiver epochs, S2): the
  -- batch lock's key and the transaction's part of `s.mu`'s deposit ghost deposited; the store
  -- registered in its backend (S6: now, if a restore left it pending); the frozen state excluded
  -- by the caller's `G`
  imod mvcc.writerInv_checkoutG s γ iprop(G ∗ □ (mvcc.slotF γ ∗ G -∗ False))
      (mvcc.slotF_excl_of γ G) _ ow $$ Hlc2 Hwi [HG] Hpinw HW Hwr
    with ⟨HL, #Hreg, ⟨HG, -⟩, ⟨%L, HwvW, Hbv, #HcertW, %HneW, Hcres⟩, Hpinw⟩
  · iframe HG HFG
  iunfold mvcc.writerL at HL
  icases HL with ⟨%ilog, %ntok, HL⟩
  iNamed HL
  icases mvcc.ghostVar_join_halves γ.wv ilog L $$ [Hwv HwvW] with ⟨Hwv, %HL⟩
  · iframe Hwv HwvW
  subst HL
  ihave Hbv := mvcc.bucketViewL_join2 γ (1 : Qp).half.half.half (1 : Qp).half.half ilog logP
    $$ [Hbv HbvP]
  · iframe Hbv HbvP
  -- the begin's callback (§3, "`Write`'s begin"): the writer's slot at the committed log and the
  -- transaction's compaction revision (the writer slot's half of `wcr` agrees with `s.mu`'s)
  iunfold mvcc.slotY at HY
  icases HY with ⟨%cy, HYa, HYp, HYr, HYw⟩
  icases mvcc.muHeld_wcr s γ cm ow.ti _ cy $$ [$Hmuh $HYw] with ⟨Hmuh, HYw, %Hcy⟩
  subst Hcy
  iunfold mvcc.writeCb at Hwcb
  imod Hwcb $$ %ilog %cm [$HYa $HYp] with ⟨HYa, HYp, HF⟩
  ihave HY : mvcc.slotY γ ilog $$ [HYa HYp HYr HYw]
  · iunfold mvcc.slotY; iexists cm; iframe HYa HYp HYr HYw
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
  iframe HQ Hback Hpinw HG Htrc
  iexists ilog, cm
  iframe Hlbc HpM HF
  isplitl
  rotate_left
  · ipureintro; exact Hclbc
  iunfold mvcc.isTxnWriteT
  iexists «$r0_ptr», W64 0
  iframe Hmw
  isplitl
  rotate_left
  · itrivial
  iunfold mvcc.storeTxnWriteIs
  iexists ow.ti, bt, Locked, chs, [], ntok, Ph, (#() : val), Dep
  simp only [named, mvcc.pendPuts_nil]
  simp only [List.replicate_zero]
  iframe Htoks Htok «$r0» Hchs Hcap Hlocked Hw Hclog Hcur Hbv Hwv HY Htko Hmuh HrevMuR HtiR HrtR Hcres Hloan Hlrd
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
