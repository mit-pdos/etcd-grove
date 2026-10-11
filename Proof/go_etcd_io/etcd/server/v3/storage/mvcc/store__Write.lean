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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.store.Write.wp_proof (hNew : mvcc.newMetricsTxnWrite.spec (GF := GF) (hG := hG)) :
    mvcc.store.Write.spec (GF := GF) (hG := hG) := by
  intro s γ trace
  wp_start as ⟨#Hs, Hrd, Htok⟩
  ihave #Hs0 : mvcc.isStore s γ $$ []
  · iexact Hs
  iunfold mvcc.isStore at Hs
  iNamed Hs
  iunfold mvcc.storeReader at Hrd
  icases Hrd with ⟨%ti2, Hrd⟩
  iNamedSuffix Hrd "R"
  (try wp_auto)
  -- `s.mu.RLock()`
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$HmuR] as ⟨Hmul, -⟩
  (try wp_auto)
  -- `tx := s.b.BatchTx()`
  iunfold mvcc.isKeyBackend at Hbk
  icases Hbk with ⟨%bi, %Hbi, #HC, #HR, #HB⟩
  subst Hbi
  (try wp_auto)
  wp_apply HB as %bt #Hbt
  (try wp_auto)
  iunfold mvcc.isBatchTx at Hbt
  icases Hbt with ⟨%Locked, #Hbt⟩
  ihave #Hbt0 : mvcc.batchTxSpec bt (mvcc.bucketView γ) (mvcc.writerRes s γ) Locked $$ []
  · iexact Hbt
  iunfold mvcc.batchTxSpec at Hbt
  icases Hbt with ⟨#HLock, -, -, -⟩
  -- `tx.LockInsideApply()`: the writer's resources
  wp_apply HLock as ⟨Hlocked, HW⟩
  (try wp_auto)
  iunfold mvcc.writerRes at HW
  iNamed HW
  (try wp_auto)
  -- `make([]*mvccpb.KeyValue, 0, 4)`
  wp_apply (wp_slice_make3 (V := Loc) (W64 0) (W64 4) (by decide)) as %chs ⟨Hchs, Hcap, -⟩
  (try wp_auto)
  wp_apply (hNew _) as %mw Hmw
  (try wp_auto)
  iapply HΦ
  iexists ilog
  iunfold mvcc.isTxnWrite
  iexists «$r0_ptr», W64 0
  iframe Hmw
  iunfold mvcc.storeTxnWriteIs
  iexists trace, ti2, bt, Locked, chs, [], ntok
  simp only [named, mvcc.pendPuts_nil]
  simp only [List.replicate_zero]
  iframe Htoks Htok «$r0» Hchs Hcap Hlocked Hw Hclog Hcur Hmul HrevMuR HtiR
  iframe #
  isplitl []
  · ipureintro; exact Hbudget
  isplitl []
  · ipureintro; rfl
  isplitl []
  · iunfold mvcc.changesAre
    iapply BigSepL.bigSepL_nil_intro
    iempintro
  ipureintro; exact Hne

end proof

end EtcdGrove
end Perennial
