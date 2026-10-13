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
  intro s γ trace P Pre Q f
  wp_start as ⟨#Hs, Hrd, Htok, Hwt, %Htrnn, #HhookC, Hpre, #Htriple⟩
  ihave #Hs0 : mvcc.isStore s γ $$ []
  · iexact Hs
  iunfold mvcc.isStore at Hs
  icases Hs with ⟨%b, %le, %ti, %lg, %P0, %f0, Hs⟩
  iNamed Hs
  iunfold mvcc.storeReader at Hrd
  icases Hrd with ⟨%ti2, Hrd⟩
  iNamedSuffix Hrd "R"
  wp_auto_lc 1
  -- the caller's hook is the store's
  imod mvcc.hookIs_agree_lc ⊤ γ P P0 f f0 $$ [$Hlc1 $HhookC $Hhook] with ⟨%Hfeq, #HPP0, #HP0P⟩
  subst Hfeq
  ihave #Htr0 : □ ({{ P0 ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) $$ []
  · iintro !> %Φ !> ⟨HP0, Hpre⟩ HΦ
    iapply Htriple $$ %Φ [HP0 Hpre] HΦ
    iframe Hpre
    iapply HP0P
    iexact HP0
  -- `s.mu.RLock()`
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HmuR] as ⟨Hmul, -⟩
  (try wp_auto)
  -- `tx := s.b.BatchTx()`
  iunfold mvcc.isKeyBackendG at Hbk
  icases Hbk with ⟨%bi, %Hbi, #HC, #HR, #HB, -⟩
  subst Hbi
  (try wp_auto)
  wp_apply HB as %bt #Hbt
  (try wp_auto)
  iunfold mvcc.isBatchTxG at Hbt
  icases Hbt with ⟨%Locked, %LockedO, #Hbt, -⟩
  ihave #Hbt0 : mvcc.batchTxSpecG bt (mvcc.bucketView γ) (mvcc.storeRT γ) (mvcc.storeWT γ)
      (mvcc.storePutOk γ) (mvcc.storeW s γ) Locked P0 f $$ []
  · iexact Hbt
  iunfold mvcc.batchTxSpecG at Hbt
  icases Hbt with ⟨#HLock, -, -, -, -⟩
  -- `tx.LockInsideApply()`: the writer's resources, the hook run on the caller's `Pre`
  ihave #HLock' := HLock $$ %Pre %Q
  wp_apply HLock' $$ [$Hpre $Htr0 $HrtR $Hwt] as ⟨Hlocked, HW, HQ, HrtR⟩
  (try wp_auto)
  ihave HW := mvcc.storeW_get s γ $$ [$Hreg $HW]
  iunfold mvcc.writerRes at HW
  iNamed HW
  (try wp_auto)
  -- `make([]*mvccpb.KeyValue, 0, 4)`
  wp_apply (wp_slice_make3 (V := Loc) (W64 0) (W64 4) (by decide)) as %chs ⟨Hchs, Hcap, -⟩
  (try wp_auto)
  wp_apply (hNew _) as %mw Hmw
  (try wp_auto)
  iapply HΦ
  iframe HQ
  iexists ilog
  iunfold mvcc.isTxnWrite
  iexists «$r0_ptr», W64 0
  iframe Hmw
  iunfold mvcc.storeTxnWriteIs
  iexists trace, ti2, bt, Locked, chs, [], ntok, P0, f
  simp only [named, mvcc.pendPuts_nil]
  simp only [List.replicate_zero]
  iframe Htoks Htok «$r0» Hchs Hcap Hlocked Hw Hclog Hcur Hbv Hmul HrevMuR HtiR HrtR
  iframe #
  isplitl []
  · ipureintro; exact Hbudget
  isplitl []
  · ipureintro; rfl
  isplitl []
  · iunfold mvcc.changesAre
    iapply BigSepL.bigSepL_nil_intro
    iempintro
  ipureintro; exact ⟨Hne, Htrnn⟩

end proof

end EtcdGrove
end Perennial
