/-
The readers' statements of the store's specs (M2, `notes/m2-plan.md`, S1, 2026-10-27; until then the
frozen statements of compaction unit 6a, `FrozenSpecs.lean`, of a store never compacted): for each
spec of `Spec/…/storage/mvcc/` that the packages above mvcc (and the watchable store) use, its
statement over the store's reader (`storeReader`) and the transactions at the tag `True`
(`<fn>.specR`), and the corollary `<fn>.spec_R : <fn>.spec → <fn>.specR`. A read transaction's
compaction revision `crev` is the one it observed (`store.Read`'s post: `crevLb γ.idx crev`), and a
range over it answers `rangeOutcomeC … crev` (`ErrCompacted` exactly below it;
`rangeOutcomeC_latest`: a latest read is never compacted). The statements that never mention the
compaction revision are the frozen ones, unchanged.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ### `store__Read` -/

/-- The readers' statement: the read transaction at the compaction revision it observed. -/
abbrev mvcc.store.Read.specR : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (mode : w32) (trace : Loc) (m : Nat) (log₀ : mvcc.Log) (te : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeReader s γ ∗ ownToks γ.revs m ∗ mvcc.idxCert γ.idx log₀ ∗
      ⌜trace ≠ null⌝ ∗ traceutil.ownTrace trace te }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Read")) (Val #mode)) (Val #trace))
  {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
      ∃ (log : mvcc.Log) (rev : w64) (crev : Int), mvcc.isTxnRead mw s γ trace log rev crev ∗
        mvcc.crevLb γ.idx crev ∗ ownToks γ.revs m ∗ mvcc.certOk γ log ∗
        ⌜log₀ <+: log ∧ log.length + m + 3 ≤ 2 ^ 63⌝ }}

open Iris.ProofMode in
/-- **The readers' statement is a corollary** (the tag `True`, no log lent, the lower bound `-1`). -/
theorem mvcc.store.Read.spec_R (h : mvcc.store.Read.spec (GF := GF) (hG := hG)) :
    mvcc.store.Read.specR (GF := GF) (hG := hG) := by
  intro s γ mode trace m log₀ te
  iintro %Φ ⟨#Hpkg, #Hs, Hrd, Hm, #Hc0, %Ht, Htrc⟩ HΦ
  ihave Hrd := mvcc.storeReader_toC s γ $$ Hrd
  imod mvcc.crevLb_neg γ.idx with #Hlb
  iapply (h s γ mode trace m log₀ te (-1) iprop(True) none) $$ %Φ [Hrd Hm Htrc]
  · iframe Hrd Hm Htrc; iframe #
    isplitr; · imodintro; itrivial
    isplitr; · ipureintro; exact Ht
    unfold mvcc.logLent; itrivial
  inext
  iintro %mw ⟨%log, %rev, %crev, Htx, Hm, #Hlb', #Hrok, %Hp, -, -⟩
  iapply HΦ
  iexists log, rev, crev
  iframe Htx Hm Hrok Hlb'
  ipureintro; exact ⟨Hp.1, Hp.2.1⟩

/-! ### `store__Write` -/

/-- The readers' statement: the write transaction at the compaction revision it observed. -/
abbrev mvcc.store.Write.specR : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (P Pre Q : IProp GF) (f : val) (te : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeReader s γ ∗ mvcc.revToken γ ∗ mvcc.storeWT γ ∗ ⌜trace ≠ null⌝ ∗
      mvcc.hookIs γ P f ∗ Pre ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗
      traceutil.ownTrace trace te }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Write")) (Val #trace))
  {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
      (∃ (ilog : mvcc.Log) (crev : Int),
        mvcc.isTxnWrite mw s γ trace ilog [] (W64 0) (W64 0) (W64 0) crev ∗ mvcc.crevLb γ.idx crev) ∗
      Q ∗ mvcc.hookIs γ P f }}

open Iris.ProofMode in
/-- **The readers' statement is a corollary** (the tag `True`, the lower bound `-1`). -/
theorem mvcc.store.Write.spec_R (h : mvcc.store.Write.spec (GF := GF) (hG := hG)) :
    mvcc.store.Write.specR (GF := GF) (hG := hG) := by
  intro s γ trace P Pre Q f te
  iintro %Φ ⟨#Hpkg, #Hs, Hrd, Htok, Hwt, %Ht, Hh, Hpre, #Htr, Htrc⟩ HΦ
  ihave Hrd := mvcc.storeReader_toC s γ $$ Hrd
  imod mvcc.crevLb_neg γ.idx with #Hlb
  iapply (h s γ trace P Pre Q f te (-1) iprop(True)) $$ %Φ [Hrd Htok Hwt Hpre Htrc Hh]
  · iframe Hrd Htok Hwt Hpre Htrc Hh; iframe #
    isplitr; · imodintro; itrivial
    ipureintro; exact Ht
  inext
  iintro %mw ⟨⟨%ilog, %crev, Htx, #Hlb', -⟩, HQ, Hh⟩
  iapply HΦ
  iframe HQ Hh
  iexists ilog, crev
  iframe Htx Hlb'

/-! ### `store__Rev` -/

/-- The readers' statement (the frozen one: it does not mention the compaction revision). -/
abbrev mvcc.store.Rev.specR : Prop :=
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
/-- **The readers' statement is a corollary.** -/
theorem mvcc.store.Rev.spec_R (h : mvcc.store.Rev.spec (GF := GF) (hG := hG)) :
    mvcc.store.Rev.specR (GF := GF) (hG := hG) := by
  intro s rv γ m log₀
  iintro %Φ ⟨#Hpkg, #HRV, #Hrv, Hrd, Htoks, #Hc0⟩ HΦ
  ihave Hrd := mvcc.storeReader_toC s γ $$ Hrd
  iapply (h s rv γ m log₀) $$ %Φ [Hrd Htoks]
  · iframe Hrd Htoks; iframe #
  inext
  iintro %v ⟨Hrd, Htoks, %log, #Hc, -, %Hp⟩
  iapply HΦ
  iframe Htoks
  isplitl [Hrd]
  · iapply mvcc.storeReader_of $$ Hrd
  iexists log
  iframe Hc
  ipureintro; exact Hp

/-! ### `storeTxnCommon__Range` -/

/-- The readers' statement: the general one at the tag `True`. -/
abbrev mvcc.storeTxnCommon.Range.specR : Prop :=
  ∀ (tr s trace ti : Loc) (rt : GoInterfaceOk) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool)
    (key endk : GoSlice) (k e : GoString) (ro : RangeOptions) (te : Bool) (crev : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeTxnReadIs tr s rt trace γ log rev crev ∗ mvcc.txReader γ rt log ∗
      mvcc.idxReader ti γ.idx ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e ∗
      mvcc.muHeld s γ crev ti ∗ traceutil.ownTrace trace te }}
    (App (App (App (App (Val (mvcc.txCommon tr @!! go.GoType.PointerType storeTxnCommon.ty @!!
      go!"Range")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗
      mvcc.idxReader ti γ.idx ∗ mvcc.muHeld s γ crev ti ∗ mvcc.txReader γ rt log ∗
      traceutil.ownTrace trace te ∗
      mvcc.rangeOutcomeC r err log rev crev (decide (endk = slice.nil)) k e ro }}

/-- **The readers' statement is a corollary** (the general one, `Z := True`). -/
theorem mvcc.storeTxnCommon.Range.spec_R
    (h : mvcc.storeTxnCommon.Range.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnCommon.Range.specR (GF := GF) (hG := hG) :=
  fun tr s trace ti rt γ log rev ctx cd todo key endk k e ro te crev =>
    h tr s trace ti rt γ log rev ctx cd todo key endk k e ro te crev iprop(True)

/-! ### `storeTxnRead__End` -/

/-- The readers' statement. -/
abbrev mvcc.storeTxnRead.End.specR : Prop :=
  ∀ (tr s trace ti : Loc) (rt : GoInterfaceOk) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64)
    (crev : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeTxnReadIs tr s rt trace γ log rev crev ∗ mvcc.txReader γ rt log ∗
      mvcc.muHeld s γ crev ti ∗
      sync.ownRWMutex (mvcc.revMuAddr s) (mvcc.revMuInv s γ) ∗ mvcc.idxReader ti γ.idx }}
    (App (Val (tr @!! go.GoType.PointerType storeTxnRead.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReader s γ }}

open Iris.ProofMode in
/-- **The readers' statement is a corollary** (`storeReader_of`). -/
theorem mvcc.storeTxnRead.End.spec_R (h : mvcc.storeTxnRead.End.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnRead.End.specR (GF := GF) (hG := hG) := by
  intro tr s trace ti rt γ log rev crev
  iintro %Φ H HΦ
  iapply (h tr s trace ti rt γ log rev crev iprop(True)) $$ %Φ [H]
  · iexact H
  inext
  iintro ⟨Hr, -⟩
  iapply HΦ
  iapply mvcc.storeReader_of $$ Hr

/-! ### `storeTxnWrite__Range` -/

/-- The readers' statement: the general one at the tag `True`. -/
abbrev mvcc.storeTxnWrite.Range.specR : Prop :=
  ∀ (trace : Loc) (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool)
    (key endk : GoSlice) (k e : GoString) (ro : RangeOptions) (te : Bool) (crev : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteIs tw s γ trace ilog pend crev ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗
      endk ↦*□ e ∗ traceutil.ownTrace trace te }}
    (App (App (App (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗
      mvcc.storeTxnWriteIs tw s γ trace ilog pend crev ∗ traceutil.ownTrace trace te ∗
      mvcc.rangeOutcomeC r err (ilog ++ [pend]) (W64 ((mvcc.writeRev ilog pend : Nat) : Int)) crev
        (decide (endk = slice.nil)) k e ro }}

/-- **The readers' statement is a corollary** (the general one, `Z := True`). -/
theorem mvcc.storeTxnWrite.Range.spec_R
    (h : mvcc.storeTxnWrite.Range.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnWrite.Range.specR (GF := GF) (hG := hG) :=
  fun trace tw s γ ilog pend ctx cd todo key endk k e ro te crev =>
    h trace tw s γ ilog pend ctx cd todo key endk k e ro te crev iprop(True)

/-! ### `storeTxnWrite__End` -/

/-- The readers' statement. -/
abbrev mvcc.storeTxnWrite.End.specR : Prop :=
  ∀ (trace : Loc) (tw s : Loc) (γ : mvcc.StoreNames) (ilog : mvcc.Log) (pend : List mvcc.Change)
    (chs : GoSlice) (ps : List Loc) (sealed : Bool) (P : IProp GF) (f : val) (crev : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.storeTxnWriteCore tw s γ trace ilog pend chs ps sealed crev ∗ mvcc.hookIs γ P f ∗ P ∗
      mvcc.certOkNext γ ilog pend ∗ mvcc.logQPre γ ilog pend }}
    (App (Val (tw @!! go.GoType.PointerType storeTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReader s γ ∗ mvcc.idxCert γ.idx (mvcc.commitLog ilog pend) ∗
      (if pend = [] then mvcc.revToken γ else iprop(True)) ∗ mvcc.logQPost γ ilog pend ∗
      mvcc.writerFrag γ }}

open Iris.ProofMode in
/-- **The readers' statement is a corollary** (`storeReader_of`). -/
theorem mvcc.storeTxnWrite.End.spec_R (h : mvcc.storeTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnWrite.End.specR (GF := GF) (hG := hG) := by
  intro trace tw s γ ilog pend chs ps sealed P f crev
  iintro %Φ H HΦ
  iapply (h trace tw s γ ilog pend chs ps sealed P f crev iprop(True) false) $$ %Φ [H]
  · iexact H
  inext
  iintro ⟨Hr, -, Hrest⟩
  iapply HΦ
  iframe Hrest
  iapply mvcc.storeReader_of $$ Hr

/-! ### `metricsTxnWrite__Range` -/

/-- The readers' statement: the general one at the tag `True`. -/
abbrev mvcc.metricsTxnWrite.Range.specR : Prop :=
  ∀ (trace : Loc) (mw s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool)
    (key endk : GoSlice) (k e : GoString) (ro : RangeOptions) (crev : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTxn mw s γ trace kind crev ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
    (App (App (App (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗ mvcc.isTxn mw s γ trace kind crev ∗
      mvcc.rangeOutcomeC r err kind.readLog kind.readRev crev (decide (endk = slice.nil)) k e ro }}

/-- **The readers' statement is a corollary** (the general one, `Z := True`). -/
theorem mvcc.metricsTxnWrite.Range.spec_R
    (h : mvcc.metricsTxnWrite.Range.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.Range.specR (GF := GF) (hG := hG) :=
  fun trace mw s γ kind ctx cd todo key endk k e ro crev =>
    h trace mw s γ kind ctx cd todo key endk k e ro crev iprop(True)

/-! ### `metricsTxnWrite__End` -/

/-- The readers' statement. -/
abbrev mvcc.metricsTxnWrite.End.specR : Prop :=
  ∀ (trace : Loc) (mw s : Loc) (γ : mvcc.StoreNames) (kind : mvcc.TxnKind) (crev : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isTxnEnd mw s γ trace kind crev ∗ mvcc.txnEndPre γ kind }}
    (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReader s γ ∗ mvcc.txnEndPost γ kind ∗ (∃ te : Bool, traceutil.ownTrace trace te) }}

open Iris.ProofMode in
/-- **The readers' statement is a corollary** (`storeReader_of`). -/
theorem mvcc.metricsTxnWrite.End.spec_R
    (h : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.End.specR (GF := GF) (hG := hG) := by
  intro trace mw s γ kind crev
  iintro %Φ H HΦ
  iapply (h trace mw s γ kind crev iprop(True)) $$ %Φ [H]
  · iexact H
  inext
  iintro ⟨Hr, -, Hpost⟩
  iapply HΦ
  iframe Hpost
  iapply mvcc.storeReader_of $$ Hr

/-! ### `txnReadWrite__Range` -/

/-- The readers' statement: the general one at the tag `True`. -/
abbrev mvcc.txnReadWrite.Range.specR : Prop :=
  ∀ (trace : Loc) (trw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool) (key endk : GoSlice)
    (k e : GoString) (ro : RangeOptions) (crev : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isRoTxnWrite trw s γ trace log rev crev ∗ mvcc.rangeCtx todo ctx cd ∗ key ↦*□ k ∗
      endk ↦*□ e }}
    (App (App (App (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜todo = true → r ≠ null⌝ ∗ mvcc.isRoTxnWrite trw s γ trace log rev crev ∗
      mvcc.rangeOutcomeC r err log rev crev (decide (endk = slice.nil)) k e ro }}

/-- **The readers' statement is a corollary** (the general one, `Z := True`). -/
theorem mvcc.txnReadWrite.Range.spec_R
    (h : mvcc.txnReadWrite.Range.spec (GF := GF) (hG := hG)) :
    mvcc.txnReadWrite.Range.specR (GF := GF) (hG := hG) :=
  fun trace trw s γ log rev ctx cd todo key endk k e ro crev =>
    h trace trw s γ log rev ctx cd todo key endk k e ro crev iprop(True)

/-! ### `txnReadWrite__End` -/

/-- The readers' statement. -/
abbrev mvcc.txnReadWrite.End.specR : Prop :=
  ∀ (trace : Loc) (trw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) (crev : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isRoTxnWrite trw s γ trace log rev crev }}
    (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReader s γ ∗ (∃ te : Bool, traceutil.ownTrace trace te) }}

open Iris.ProofMode in
/-- **The readers' statement is a corollary** (`storeReader_of`). -/
theorem mvcc.txnReadWrite.End.spec_R (h : mvcc.txnReadWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.txnReadWrite.End.specR (GF := GF) (hG := hG) := by
  intro trace trw s γ log rev crev
  iintro %Φ H HΦ
  iapply (h trace trw s γ log rev crev iprop(True)) $$ %Φ [H]
  · iexact H
  inext
  iintro ⟨Hr, -, Htrc⟩
  iapply HΦ
  iframe Htrc
  iapply mvcc.storeReader_of $$ Hr

/-! ### `readView__Range` -/

/-- The readers' statement: the range at the compaction revision the read view's transaction
observed. -/
abbrev mvcc.readView.Range.specR : Prop :=
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
      ∃ (log : mvcc.Log) (rev : w64) (crev : Int), mvcc.idxCert γ.idx log ∗ mvcc.crevLb γ.idx crev ∗
        ⌜log ≠ [] ∧ rev = W64 ((log.length : Int) - 1) ∧ -1 ≤ crev⌝ ∗
        mvcc.rangeOutcomeC r err log rev crev (decide (endk = slice.nil)) k e ro }}

open Iris.ProofMode in
/-- **The readers' statement is a corollary** (the lower bound `-1`). -/
theorem mvcc.readView.Range.spec_R (h : mvcc.readView.Range.spec (GF := GF) (hG := hG)) :
    mvcc.readView.Range.specR (GF := GF) (hG := hG) := by
  intro rv s γ ctx cd key endk k e ro
  iintro %Φ ⟨#Hpkg, #Hrv, Hrd, #Hctx, #Hkey, #Hend⟩ HΦ
  ihave Hrd := mvcc.storeReader_toC s γ $$ Hrd
  imod mvcc.crevLb_neg γ.idx with #Hlb
  ihave #Hctx' : mvcc.rangeCtx false ctx cd $$ []
  · simp only [mvcc.rangeCtx, Bool.false_eq_true, ↓reduceIte]; iexact Hctx
  iapply (h rv s γ ctx cd false key endk k e ro (-1)) $$ %Φ [Hrd]
  · iframe Hrd; iframe #
  inext
  iintro %r %err ⟨-, Hrd, %log, %rev, %crev, #Hc, #Hlb', %Hp, Hout⟩
  iapply HΦ
  isplitl [Hrd]
  · iapply mvcc.storeReader_of $$ Hrd
  iexists log, rev, crev
  iframe Hc Hlb' Hout
  ipureintro; exact ⟨Hp.1, Hp.2.1, Hp.2.2.2⟩

/-! ### `readView__Rev` -/

/-- The readers' statement (the frozen one: it does not mention the compaction revision). -/
abbrev mvcc.readView.Rev.specR : Prop :=
  ∀ (rv s : Loc) (γ : mvcc.StoreNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isReadView rv s γ ∗ mvcc.storeReader s γ }}
    (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"Rev")) (Val #()))
  {{ (v : w64), RET #v; mvcc.storeReader s γ ∗
      ∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗ ⌜log ≠ [] ∧ v = W64 ((log.length : Int) - 1)⌝ }}

open Iris.ProofMode in
/-- **The readers' statement is a corollary.** -/
theorem mvcc.readView.Rev.spec_R (h : mvcc.readView.Rev.spec (GF := GF) (hG := hG)) :
    mvcc.readView.Rev.specR (GF := GF) (hG := hG) := by
  intro rv s γ
  iintro %Φ ⟨#Hpkg, #Hrv, Hrd⟩ HΦ
  ihave Hrd := mvcc.storeReader_toC s γ $$ Hrd
  iapply (h rv s γ) $$ %Φ [Hrd]
  · iframe Hrd; iframe #
  inext
  iintro %v ⟨Hrd, Hpost⟩
  iapply HΦ
  iframe Hpost
  iapply mvcc.storeReader_of $$ Hrd

/-! ### `readView__FirstRev` -/

/-- The readers' statement: the compaction revision the read view's transaction observed. -/
abbrev mvcc.readView.FirstRev.specR : Prop :=
  ∀ (rv s : Loc) (γ : mvcc.StoreNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isReadView rv s γ ∗ mvcc.storeReader s γ }}
    (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"FirstRev")) (Val #()))
  {{ (v : w64), RET #v; mvcc.storeReader s γ ∗
      ∃ crev : Int, mvcc.crevLb γ.idx crev ∗ ⌜v = W64 crev ∧ -1 ≤ crev⌝ }}

open Iris.ProofMode in
/-- **The readers' statement is a corollary** (the lower bound `-1`). -/
theorem mvcc.readView.FirstRev.spec_R (h : mvcc.readView.FirstRev.spec (GF := GF) (hG := hG)) :
    mvcc.readView.FirstRev.specR (GF := GF) (hG := hG) := by
  intro rv s γ
  iintro %Φ ⟨#Hpkg, #Hrv, Hrd⟩ HΦ
  ihave Hrd := mvcc.storeReader_toC s γ $$ Hrd
  imod mvcc.crevLb_neg γ.idx with #Hlb
  iapply (h rv s γ (-1)) $$ %Φ [Hrd]
  · iframe Hrd; iframe #
  inext
  iintro %v ⟨Hrd, %crev, #Hlb', %Hp⟩
  iapply HΦ
  isplitl [Hrd]
  · iapply mvcc.storeReader_of $$ Hrd
  iexists crev
  iframe Hlb'
  ipureintro; exact ⟨Hp.1, Hp.2.2⟩

/-! ### `watchableStore__rev` -/

/-- The readers' statement (the frozen one: it does not mention the compaction revision). -/
abbrev mvcc.watchableStore.rev.specR : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (oa : Option (Qp × mvcc.Log)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ mvcc.storeReader st γ.st ∗ mvcc.logLent γ.st.idx oa }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"rev")) (Val #()))
  {{ (r : w64), RET #r; mvcc.storeReader st γ.st ∗ mvcc.logLent γ.st.idx oa ∗
      ∃ log : mvcc.Log, mvcc.idxCert γ.st.idx log ∗ ⌜log ≠ [] ∧ r = W64 ((log.length : Int) - 1) ∧
        2 ≤ log.length ∧ log.length < 2 ^ 63 ∧ ∀ q L, oa = some (q, L) → log = L⌝ }}

open Iris.ProofMode in
/-- **The readers' statement is a corollary.** -/
theorem mvcc.watchableStore.rev.spec_R (h : mvcc.watchableStore.rev.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.rev.specR (GF := GF) (hG := hG) := by
  intro s st γ oa
  iintro %Φ ⟨#Hpkg, #Hws, Hrd, HoA⟩ HΦ
  ihave Hrd := mvcc.storeReader_toC st γ.st $$ Hrd
  iapply (h s st γ oa) $$ %Φ [Hrd HoA]
  · iframe Hrd HoA; iframe #
  inext
  iintro %v ⟨Hrd, Hpost⟩
  iapply HΦ
  iframe Hpost
  iapply mvcc.storeReader_of $$ Hrd

end spec

end EtcdGrove
end Perennial
