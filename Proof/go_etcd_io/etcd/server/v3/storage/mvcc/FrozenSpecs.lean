/-
The frozen statements of the store's reader specs (2026-10-13, compaction unit 6a; `notes/decisions.md`,
"Compaction-aware readers (unit 6a)"): for each spec of `Spec/…/storage/mvcc/` whose shape changed
when the readers became compaction-aware, its statement before unit 6a (`<fn>.specFrozen`: a store
never compacted, `storeReader`, `rangeOutcome`, the transactions at their default compaction
revision `-1` and tag `crevFrozen γ`) and the corollary `<fn>.spec_frozen : <fn>.spec →
<fn>.specFrozen`. The proofs of the packages above mvcc (and the watchable store's) take the
general spec as a hypothesis and apply the corollary.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Read
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Write
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnRead__End
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__End
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__End
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.readView__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.readView__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.readView__FirstRev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__rev

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ### `store__Read` -/

/-- The frozen statement (before unit 6a): a reader of a store never compacted. -/
abbrev mvcc.store.Read.specFrozen : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (mode : w32) (trace : Loc) (m : Nat) (log₀ : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeReader s γ ∗ ownToks γ.revs m ∗ mvcc.idxCert γ.idx log₀ ∗
      ⌜trace ≠ null⌝ }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Read")) (Val #mode)) (Val #trace))
  {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
      ∃ (log : mvcc.Log) (rev : w64), mvcc.isTxnRead mw s γ log rev ∗ ownToks γ.revs m ∗
        ⌜log₀ <+: log ∧ log.length + m + 3 ≤ 2 ^ 63⌝ }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary**: the frozen fact makes the observed compaction
revision `-1` (`isTxnRead_frozen`). -/
theorem mvcc.store.Read.spec_frozen (h : mvcc.store.Read.spec (GF := GF) (hG := hG)) :
    mvcc.store.Read.specFrozen (GF := GF) (hG := hG) := by
  intro s γ mode trace m log₀
  iintro %Φ ⟨#Hpkg, #Hs, Hrd, Hm, #Hc0, %Ht⟩ HΦ
  icases mvcc.storeReader_toC s γ $$ Hrd with ⟨Hrd, #Hf⟩
  imod mvcc.crevLb_neg γ.idx with #Hlb
  iapply wp_fupd
  iapply (h s γ mode trace m log₀ (-1) (mvcc.crevFrozen γ)) $$ %(fun v => iprop(|={⊤}=> Φ v))
    [Hrd Hm]
  · iframe Hrd Hm; iframe #; ipureintro; exact Ht
  inext
  iintro %mw ⟨%log, %rev, %crev, Htx, Hm, #Hlb', %Hp⟩
  imod mvcc.isTxnRead_frozen mw s γ log rev crev $$ Htx with ⟨Htx, %Hcr⟩
  subst Hcr
  imodintro
  iapply HΦ
  iexists log, rev
  iframe Htx Hm
  ipureintro; exact ⟨Hp.1, Hp.2.1⟩

/-! ### `store__Write` -/

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.store.Write.specFrozen : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (P Pre Q : IProp GF) (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeReader s γ ∗ mvcc.revToken γ ∗ mvcc.storeWT γ ∗ ⌜trace ≠ null⌝ ∗
      mvcc.hookIs γ P f ∗ Pre ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Write")) (Val #trace))
  {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
      (∃ ilog : mvcc.Log, mvcc.isTxnWrite mw s γ ilog [] (W64 0) (W64 0) (W64 0)) ∗ Q }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (`isTxnWrite_frozen`). -/
theorem mvcc.store.Write.spec_frozen (h : mvcc.store.Write.spec (GF := GF) (hG := hG)) :
    mvcc.store.Write.specFrozen (GF := GF) (hG := hG) := by
  intro s γ trace P Pre Q f
  iintro %Φ ⟨#Hpkg, #Hs, Hrd, Htok, Hwt, %Ht, #Hh, Hpre, #Htr⟩ HΦ
  icases mvcc.storeReader_toC s γ $$ Hrd with ⟨Hrd, #Hf⟩
  imod mvcc.crevLb_neg γ.idx with #Hlb
  iapply wp_fupd
  iapply (h s γ trace P Pre Q f (-1) (mvcc.crevFrozen γ)) $$ %(fun v => iprop(|={⊤}=> Φ v))
    [Hrd Htok Hwt Hpre]
  · iframe Hrd Htok Hwt Hpre; iframe #; ipureintro; exact Ht
  inext
  iintro %mw ⟨⟨%ilog, %crev, Htx, #Hlb', %Hc⟩, HQ⟩
  imod mvcc.isTxnWrite_frozen mw s γ ilog [] (W64 0) (W64 0) (W64 0) crev $$ Htx with ⟨Htx, %Hcr⟩
  subst Hcr
  imodintro
  iapply HΦ
  iframe HQ
  iexists ilog
  iexact Htx

/-! ### `store__Rev` -/

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.store.Rev.specFrozen : Prop :=
  ∀ (s rv : Loc) (γ : mvcc.StoreNames) (m : Nat) (log₀ : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      s.[store, go!"ReadView"] ↦□
        (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
      mvcc.isReadView rv s γ ∗ mvcc.storeReader s γ ∗ ownToks γ.revs m ∗
      mvcc.idxCert γ.idx log₀ }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Rev")) (Val #()))
  {{ (v : w64), RET #v; mvcc.storeReader s γ ∗ ownToks γ.revs m ∗
      ∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗
        ⌜log₀ <+: log ∧ log.length + m + 3 ≤ 2 ^ 63 ∧ log ≠ [] ∧
          v = W64 ((log.length : Int) - 1)⌝ }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (the frozen fact framed). -/
theorem mvcc.store.Rev.spec_frozen (h : mvcc.store.Rev.spec (GF := GF) (hG := hG)) :
    mvcc.store.Rev.specFrozen (GF := GF) (hG := hG) := by
  intro s rv γ m log₀
  iintro %Φ ⟨#Hpkg, #HRV, #Hrv, Hrd, Htoks, #Hc0⟩ HΦ
  icases mvcc.storeReader_toC s γ $$ Hrd with ⟨Hrd, #Hf⟩
  iapply (h s rv γ m log₀) $$ %Φ [Hrd Htoks]
  · iframe Hrd Htoks; iframe #
  inext
  iintro %v ⟨Hrd, Hpost⟩
  iapply HΦ
  iframe Hpost
  iapply mvcc.storeReader_of $$ [$Hrd $Hf]

/-! ### `storeTxnCommon__Range` -/

/-- The frozen statement (before unit 6a): of a store not compacted (`storeTxnReadIs` at its
defaults, `muHeld` at `-1`), the outcome is `rangeOutcome`. -/
abbrev mvcc.storeTxnCommon.Range.specFrozen : Prop :=
  ∀ (tr s trace ti : Loc) (rt : GoInterfaceOk) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool)
    (key endk : GoSlice) (k e : GoString) (ro : RangeOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeTxnReadIs tr s rt trace γ log rev ∗ mvcc.txReader γ rt log ∗
      s.[store, go!"kvindex"] ↦□ (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      mvcc.idxReader ti γ.idx ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e ∗
      mvcc.muHeld s γ (-1) }}
    (App (App (App (App (Val (mvcc.txCommon tr @!! go.GoType.PointerType storeTxnCommon.ty @!!
      go!"Range")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗
      mvcc.idxReader ti γ.idx ∗ mvcc.muHeld s γ (-1) ∗ mvcc.txReader γ rt log ∗
      mvcc.rangeOutcome r err log rev (decide (endk = slice.nil)) k e ro }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (`crev = -1`, `rangeOutcomeC_neg`). -/
theorem mvcc.storeTxnCommon.Range.spec_frozen
    (h : mvcc.storeTxnCommon.Range.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnCommon.Range.specFrozen (GF := GF) (hG := hG) := by
  intro tr s trace ti rt γ log rev ctx cd todo key endk k e ro
  iintro %Φ ⟨#Hpkg, #Hs, #Htr, Hrd, #Hidx, Hti, #Hctx, #Hkey, #Hend, Hmu⟩ HΦ
  ihave %Hrv := mvcc.storeTxnReadIs_rev tr s rt trace γ log rev (-1) (mvcc.crevFrozen γ) $$ Htr
  iapply (h tr s trace ti rt γ log rev ctx cd todo key endk k e ro (-1) (mvcc.crevFrozen γ))
    $$ %Φ [Hrd Hti Hmu]
  · iframe Hrd Hti Hmu; iframe #
  inext
  iintro %r %err ⟨%Ht, Hti, Hmu, Hrd, Hout⟩
  iapply HΦ
  iframe Hti Hmu Hrd
  isplitl []
  · ipureintro; exact Ht
  iapply mvcc.rangeOutcomeC_neg _ _ _ _ _ _ _ _ Hrv.1 $$ Hout

/-! ### `storeTxnRead__End` -/

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.storeTxnRead.End.specFrozen : Prop :=
  ∀ (tr s trace ti : Loc) (rt : GoInterfaceOk) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeTxnReadIs tr s rt trace γ log rev ∗ mvcc.txReader γ rt log ∗
      s.[store, go!"kvindex"] ↦□ (interface.mkOk (go.GoType.PointerType treeIndex.ty) #ti : GoInterface) ∗
      mvcc.muHeld s γ (-1) ∗
      sync.ownRWMutex (mvcc.revMuAddr s) (mvcc.revMuInv s γ) ∗ mvcc.idxReader ti γ.idx }}
    (App (Val (tr @!! go.GoType.PointerType storeTxnRead.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReader s γ }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (`storeReader_of`). -/
theorem mvcc.storeTxnRead.End.spec_frozen (h : mvcc.storeTxnRead.End.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnRead.End.specFrozen (GF := GF) (hG := hG) := by
  intro tr s trace ti rt γ log rev
  iintro %Φ H HΦ
  iapply (h tr s trace ti rt γ log rev (-1) (mvcc.crevFrozen γ)) $$ %Φ [H]
  · iexact H
  inext
  iintro ⟨Hr, #Hf⟩
  iapply HΦ
  iapply mvcc.storeReader_of $$ [$Hr $Hf]

/-! ### `storeTxnWrite__Range` -/

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.storeTxnWrite.Range.specFrozen : Prop :=
  ∀ (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool)
    (key endk : GoSlice) (k e : GoString) (ro : RangeOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteIs tw s γ ilog pend ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
    (App (App (App (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗
      mvcc.storeTxnWriteIs tw s γ ilog pend ∗
      mvcc.rangeOutcome r err (ilog ++ [pend]) (W64 ((mvcc.writeRev ilog pend : Nat) : Int))
        (decide (endk = slice.nil)) k e ro }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (`crev = -1`, `rangeOutcomeC_neg`). -/
theorem mvcc.storeTxnWrite.Range.spec_frozen
    (h : mvcc.storeTxnWrite.Range.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnWrite.Range.specFrozen (GF := GF) (hG := hG) := by
  intro tw s γ ilog pend ctx cd todo key endk k e ro
  iintro %Φ ⟨#Hpkg, Htw, #Hctx, #Hkey, #Hend⟩ HΦ
  iapply (h tw s γ ilog pend ctx cd todo key endk k e ro (-1) (mvcc.crevFrozen γ)) $$ %Φ [Htw]
  · iframe Htw; iframe #
  inext
  iintro %r %err ⟨%Ht, Htw, Hout⟩
  ihave %Hrv := mvcc.storeTxnWriteIs_writeRev tw s γ ilog pend (-1) (mvcc.crevFrozen γ) $$ Htw
  iapply HΦ
  iframe Htw
  isplitl []
  · ipureintro; exact Ht
  iapply mvcc.rangeOutcomeC_neg _ _ _ _ _ _ _ _ Hrv $$ Hout

/-! ### `storeTxnWrite__End` -/

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.storeTxnWrite.End.specFrozen : Prop :=
  ∀ (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (chs : GoSlice) (ps : List Loc) (sealed : Bool) (P : IProp GF) (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteCore tw s γ ilog pend chs ps sealed ∗ mvcc.hookIs γ P f ∗ P }}
    (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReader s γ ∗ mvcc.idxCert γ.idx (mvcc.commitLog ilog pend) ∗
      (if pend = [] then mvcc.revToken γ else iprop(True)) }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (`storeReader_of`). -/
theorem mvcc.storeTxnWrite.End.spec_frozen (h : mvcc.storeTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnWrite.End.specFrozen (GF := GF) (hG := hG) := by
  intro tw s γ ilog pend chs ps sealed P f
  iintro %Φ H HΦ
  iapply (h tw s γ ilog pend chs ps sealed P f (-1) (mvcc.crevFrozen γ)) $$ %Φ [H]
  · iexact H
  inext
  iintro ⟨Hr, #Hf, Hrest⟩
  iapply HΦ
  iframe Hrest
  iapply mvcc.storeReader_of $$ [$Hr $Hf]

/-! ### `metricsTxnWrite__Range` -/

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.metricsTxnWrite.Range.specFrozen : Prop :=
  ∀ (mw s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool)
    (key endk : GoSlice) (k e : GoString) (ro : RangeOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTxn mw s γ kind ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
    (App (App (App (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗ mvcc.isTxn mw s γ kind ∗
      mvcc.rangeOutcome r err kind.readLog kind.readRev (decide (endk = slice.nil)) k e ro }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (`crev = -1`, `rangeOutcomeC_neg`). -/
theorem mvcc.metricsTxnWrite.Range.spec_frozen
    (h : mvcc.metricsTxnWrite.Range.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.Range.specFrozen (GF := GF) (hG := hG) := by
  intro mw s γ kind ctx cd todo key endk k e ro
  iintro %Φ ⟨#Hpkg, Htx, #Hctx, #Hkey, #Hend⟩ HΦ
  iapply (h mw s γ kind ctx cd todo key endk k e ro (-1) (mvcc.crevFrozen γ)) $$ %Φ [Htx]
  · iframe Htx; iframe #
  inext
  iintro %r %err ⟨%Ht, Htx, Hout⟩
  icases mvcc.isTxn_readRev mw s γ kind (-1) (mvcc.crevFrozen γ) $$ Htx with ⟨Htx, %Hrv⟩
  iapply HΦ
  iframe Htx
  isplitl []
  · ipureintro; exact Ht
  iapply mvcc.rangeOutcomeC_neg _ _ _ _ _ _ _ _ Hrv $$ Hout

/-! ### `metricsTxnWrite__End` -/

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.metricsTxnWrite.End.specFrozen : Prop :=
  ∀ (mw s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isTxnEnd mw s γ kind ∗
      mvcc.txnEndPre γ kind }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReader s γ ∗ mvcc.txnEndPost γ kind }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (`storeReader_of`). -/
theorem mvcc.metricsTxnWrite.End.spec_frozen
    (h : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.End.specFrozen (GF := GF) (hG := hG) := by
  intro mw s γ kind
  iintro %Φ H HΦ
  iapply (h mw s γ kind (-1) (mvcc.crevFrozen γ)) $$ %Φ [H]
  · iexact H
  inext
  iintro ⟨Hr, #Hf, Hpost⟩
  iapply HΦ
  iframe Hpost
  iapply mvcc.storeReader_of $$ [$Hr $Hf]

/-! ### `txnReadWrite__Range` -/

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.txnReadWrite.Range.specFrozen : Prop :=
  ∀ (trw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool) (key endk : GoSlice)
    (k e : GoString) (ro : RangeOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isRoTxnWrite trw s γ log rev ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗
      endk ↦*□ e }}
    (App (App (App (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗ mvcc.isRoTxnWrite trw s γ log rev ∗
      mvcc.rangeOutcome r err log rev (decide (endk = slice.nil)) k e ro }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (`crev = -1`, `rangeOutcomeC_neg`). -/
theorem mvcc.txnReadWrite.Range.spec_frozen
    (h : mvcc.txnReadWrite.Range.spec (GF := GF) (hG := hG)) :
    mvcc.txnReadWrite.Range.specFrozen (GF := GF) (hG := hG) := by
  intro trw s γ log rev ctx cd todo key endk k e ro
  iintro %Φ ⟨#Hpkg, Htx, #Hctx, #Hkey, #Hend⟩ HΦ
  iapply (h trw s γ log rev ctx cd todo key endk k e ro (-1) (mvcc.crevFrozen γ)) $$ %Φ [Htx]
  · iframe Htx; iframe #
  inext
  iintro %r %err ⟨%Ht, Htx, Hout⟩
  ihave %Hrv : ⌜0 ≤ sint.Z rev⌝ $$ [Htx]
  · iunfold mvcc.isRoTxnWrite at Htx
    icases Htx with ⟨%mw, -, Htx⟩
    iunfold mvcc.isTxnRead at Htx
    iNamed Htx
    ihave %Hr := mvcc.storeTxnReadIs_rev tr s rt trace γ log rev (-1) (mvcc.crevFrozen γ) $$ Htr
    ipureintro; exact Hr.1
  iapply HΦ
  iframe Htx
  isplitl []
  · ipureintro; exact Ht
  iapply mvcc.rangeOutcomeC_neg _ _ _ _ _ _ _ _ Hrv $$ Hout

/-! ### `txnReadWrite__End` -/

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.txnReadWrite.End.specFrozen : Prop :=
  ∀ (trw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isRoTxnWrite trw s γ log rev }}
    (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReader s γ }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (`storeReader_of`). -/
theorem mvcc.txnReadWrite.End.spec_frozen (h : mvcc.txnReadWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.txnReadWrite.End.specFrozen (GF := GF) (hG := hG) := by
  intro trw s γ log rev
  iintro %Φ H HΦ
  iapply (h trw s γ log rev (-1) (mvcc.crevFrozen γ)) $$ %Φ [H]
  · iexact H
  inext
  iintro ⟨Hr, #Hf⟩
  iapply HΦ
  iapply mvcc.storeReader_of $$ [$Hr $Hf]

/-! ### `readView__Range` -/

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.readView.Range.specFrozen : Prop :=
  ∀ (rv s : Loc) (γ : mvcc.StoreNames)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (key endk : GoSlice) (k e : GoString)
    (ro : RangeOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isReadView rv s γ ∗ mvcc.storeReader s γ ∗
      context.isContext ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
    (App (App (App (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      mvcc.storeReader s γ ∗
      ∃ (log : mvcc.Log) (rev : w64), mvcc.idxCert γ.idx log ∗
        ⌜log ≠ [] ∧ rev = W64 ((log.length : Int) - 1)⌝ ∗
        mvcc.rangeOutcome r err log rev (decide (endk = slice.nil)) k e ro }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary**: the frozen fact bounds the observed compaction
revision by `-1` (`crevFrozen_lb`), and the read's revision is not negative (`rangeOutcomeC_neg`). -/
theorem mvcc.readView.Range.spec_frozen (h : mvcc.readView.Range.spec (GF := GF) (hG := hG)) :
    mvcc.readView.Range.specFrozen (GF := GF) (hG := hG) := by
  intro rv s γ ctx cd key endk k e ro
  iintro %Φ ⟨#Hpkg, #Hrv, Hrd, #Hctx, #Hkey, #Hend⟩ HΦ
  icases mvcc.storeReader_toC s γ $$ Hrd with ⟨Hrd, #Hf⟩
  imod mvcc.crevLb_neg γ.idx with #Hlb
  iapply wp_fupd
  iapply (h rv s γ ctx cd key endk k e ro (-1)) $$ %(fun v => iprop(|={⊤}=> Φ v)) [Hrd]
  · iframe Hrd; iframe #
  inext
  iintro %r %err ⟨Hrd, %log, %rev, %crev, #Hc, #Hlb', %Hp, Hout⟩
  imod mvcc.crevFrozen_lb γ crev Hp.2.2.2 $$ Hf Hlb' with %Hcr
  subst Hcr
  ihave %Hrv := mvcc.idxCert_lastRev γ log Hp.1 $$ Hc
  imodintro
  iapply HΦ
  isplitl [Hrd]
  · iapply mvcc.storeReader_of $$ [$Hrd $Hf]
  iexists log, rev
  iframe Hc
  isplitl []
  · ipureintro; exact ⟨Hp.1, Hp.2.1⟩
  iapply mvcc.rangeOutcomeC_neg _ _ _ _ _ _ _ _ (by rw [Hp.2.1]; exact Hrv) $$ Hout

/-! ### `readView__Rev` -/

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.readView.Rev.specFrozen : Prop :=
  ∀ (rv s : Loc) (γ : mvcc.StoreNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isReadView rv s γ ∗ mvcc.storeReader s γ }}
    (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"Rev")) (Val #()))
  {{ (v : w64), RET #v; mvcc.storeReader s γ ∗
      ∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗ ⌜log ≠ [] ∧ v = W64 ((log.length : Int) - 1)⌝ }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (the frozen fact framed). -/
theorem mvcc.readView.Rev.spec_frozen (h : mvcc.readView.Rev.spec (GF := GF) (hG := hG)) :
    mvcc.readView.Rev.specFrozen (GF := GF) (hG := hG) := by
  intro rv s γ
  iintro %Φ ⟨#Hpkg, #Hrv, Hrd⟩ HΦ
  icases mvcc.storeReader_toC s γ $$ Hrd with ⟨Hrd, #Hf⟩
  iapply (h rv s γ) $$ %Φ [Hrd]
  · iframe Hrd; iframe #
  inext
  iintro %v ⟨Hrd, Hpost⟩
  iapply HΦ
  iframe Hpost
  iapply mvcc.storeReader_of $$ [$Hrd $Hf]

/-! ### `readView__FirstRev` -/

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.readView.FirstRev.specFrozen : Prop :=
  ∀ (rv s : Loc) (γ : mvcc.StoreNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isReadView rv s γ ∗ mvcc.storeReader s γ }}
    (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"FirstRev")) (Val #()))
  {{ RET #(W64 (-1) : w64); mvcc.storeReader s γ }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (`crevFrozen_lb`: the revision is `-1`). -/
theorem mvcc.readView.FirstRev.spec_frozen (h : mvcc.readView.FirstRev.spec (GF := GF) (hG := hG)) :
    mvcc.readView.FirstRev.specFrozen (GF := GF) (hG := hG) := by
  intro rv s γ
  iintro %Φ ⟨#Hpkg, #Hrv, Hrd⟩ HΦ
  icases mvcc.storeReader_toC s γ $$ Hrd with ⟨Hrd, #Hf⟩
  imod mvcc.crevLb_neg γ.idx with #Hlb
  iapply wp_fupd
  iapply (h rv s γ (-1)) $$ %(fun v => iprop(|={⊤}=> Φ v)) [Hrd]
  · iframe Hrd; iframe #
  inext
  iintro %v ⟨Hrd, %crev, #Hlb', %Hp⟩
  imod mvcc.crevFrozen_lb γ crev Hp.2.2 $$ Hf Hlb' with %Hcr
  subst Hcr
  obtain ⟨rfl, -⟩ := Hp
  imodintro
  iapply HΦ
  iapply mvcc.storeReader_of $$ [$Hrd $Hf]

/-! ### `watchableStore__rev` -/

/-- The frozen statement (before unit 6a). -/
abbrev mvcc.watchableStore.rev.specFrozen : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ mvcc.storeReader st γ.st }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"rev")) (Val #()))
  {{ (r : w64), RET #r; mvcc.storeReader st γ.st ∗
      ∃ log : mvcc.Log, mvcc.idxCert γ.st.idx log ∗ ⌜log ≠ [] ∧ r = W64 ((log.length : Int) - 1)⌝ }}

open Iris.ProofMode in
/-- **The frozen statement is a corollary** (the frozen fact framed). -/
theorem mvcc.watchableStore.rev.spec_frozen (h : mvcc.watchableStore.rev.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.rev.specFrozen (GF := GF) (hG := hG) := by
  intro s st γ
  iintro %Φ ⟨#Hpkg, #Hws, Hrd⟩ HΦ
  icases mvcc.storeReader_toC st γ.st $$ Hrd with ⟨Hrd, #Hf⟩
  iapply (h s st γ) $$ %Φ [Hrd]
  · iframe Hrd; iframe #
  inext
  iintro %v ⟨Hrd, Hpost⟩
  iapply HΦ
  iframe Hpost
  iapply mvcc.storeReader_of $$ [$Hrd $Hf]

end spec

end EtcdGrove
end Perennial
