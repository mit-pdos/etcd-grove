/-
**M2, the storage side: Draft** (`notes/m2-storage-plan.md`; the backend-cmp Probe's P3, S1-S3,
`notes/spec-first-study/backend-probe.md`). Draft statements and laws only, imported by nothing but
the server side's Draft (`etcdserver/M2StorageDraft.lean`): each `…D` here is what an existing
definition or spec becomes at the switch, written in full so the review reads real Lean; nothing is
switched, nothing assumed (no `axiom`, no `sorry`).

- **P3, the watchable store in compaction mode.** `newWatchableStore` freezes its store's
  compaction revision in every mode today (`crevFrozen_alloc`, kept in `isWatchableStore`'s
  `Hfrz`). Drafted: the frozen fact by the mode (`wsFrozenM`, `True` when the store compacts), and
  the compaction right's half of the revision's authority handed to the caller in compaction mode
  (`crevRightM`), beside the closer: the caller makes the right (`compactRight_of_wsCloser`) only
  after its last error return (Go's deferred `kv.Close()`, `server.go:376-381`).
  `newWatchableStore`'s proof needs two changes for it: `crevRight_split` in place of
  `crevFrozen_alloc`, and `isWatchableStoreD` built with its result. (A copy of the proof with them
  was tried here: it elaborates up to the lease deleter `rdIs`, whose `watchableStore.Write`
  takes today's `isWatchableStore`; at the switch the predicate is redefined in place, so that
  step needs nothing. Not kept: a proof against a second name proves nothing more.)
- **No watchers in compaction mode** (M2's round 1, the user's): the "no compactor" fact is
  `crevFrozen γ.st` itself (persistent: an off server has it, `isWatchableStoreD_frozen`); the watch
  API takes it (`NewWatchStream.specD`), and the watch-store invariant holds `wsWatchFrozen` (no
  watcher, or the fact), so that `syncWatchers`' non-empty branch, the only user of `Hfrz`, finds it
  there. At `cm = false` every statement reads as today: `wsFrozenM` is `crevFrozen`
  (`isWatchableStoreD_off`) and `crevRightM` is `True` (`crevRightM_off`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatchableStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.New
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__NewWatchStream
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherGroup
public import Spec.go_uber_org.zap.NewNop
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Write
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchFrac
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewWatchableLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InstanceLaws

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ## The mode-gated facts -/

/-- **The frozen fact, by the mode** (draft of `isWatchableStore`'s `Hfrz`): a store that does not
compact (`¬ kbCmpM γs.kb`: today's servers, `cm = false`) is frozen (`crevFrozen`); a compacting
one is not. The mode is the logical names' (`γs.kb`, the boot backend's): no restore in compaction
mode, so it never changes. -/
def mvcc.wsFrozenM (γs : mvcc.StoreNames) : IProp GF :=
  if mvcc.kbCmpM γs.kb then iprop(True) else mvcc.crevFrozen γs

instance mvcc.wsFrozenM_persistent (γs : mvcc.StoreNames) :
    Persistent (mvcc.wsFrozenM (GF := GF) γs) := by
  unfold mvcc.wsFrozenM; split <;> infer_instance

/-- **The compaction right's half of the revision's authority, by the mode** (draft; a new conjunct
of `newWatchableStore`'s and `New`'s posts): in compaction mode the caller gets it (and makes the
compaction right of it with the closer, `compactRight_of_wsCloser`); otherwise nothing, the store
being frozen. -/
def mvcc.crevRightM (kb : Option mvcc.KBReal) (γs : mvcc.StoreNames) : IProp GF :=
  if mvcc.kbCmpM kb then mvcc.crevUB γs.idx (1 : Qp).half (-1) else iprop(True)

/-- At `cm = false` the new conjunct is `True` (the posts read as today). -/
theorem mvcc.crevRightM_off (kb : Option mvcc.KBReal) (γs : mvcc.StoreNames)
    (h : ¬ mvcc.kbCmpM kb) : mvcc.crevRightM (GF := GF) kb γs ⊣⊢ iprop(True) := by
  unfold mvcc.crevRightM; simp only [h, ↓reduceIte]; exact .rfl

/-- At `cm = false` the frozen fact is `crevFrozen`. -/
theorem mvcc.wsFrozenM_off (γs : mvcc.StoreNames) (h : ¬ mvcc.kbCmpM γs.kb) :
    mvcc.wsFrozenM (GF := GF) γs ⊣⊢ mvcc.crevFrozen γs := by
  unfold mvcc.wsFrozenM; simp only [h, ↓reduceIte]; exact .rfl

/-- `newWatchableStore`'s step, by the mode: the authority's half frozen (off) or handed out (on). -/
theorem mvcc.crevRight_split (kb : Option mvcc.KBReal) (γs : mvcc.StoreNames) (hk : γs.kb = kb) :
    mvcc.crevUB (GF := GF) γs.idx (1 : Qp).half (-1) ⊢
      |={⊤}=> mvcc.wsFrozenM γs ∗ mvcc.crevRightM kb γs := by
  unfold mvcc.wsFrozenM mvcc.crevRightM
  subst hk
  by_cases h : mvcc.kbCmpM γs.kb
  · simp only [h, ↓reduceIte]
    iintro H; imodintro; iframe H
  · simp only [h, ↓reduceIte]
    iintro H
    imod mvcc.crevFrozen_alloc γs ⊤ $$ H with #Hf
    imodintro; iframe Hf

/-! ## The watchable store, drafted -/

/-- **Draft of `isWatchableStore`**: `Hfrz` by the mode (`wsFrozenM`); otherwise the same. -/
def mvcc.isWatchableStoreD (s st : Loc) (γ : mvcc.WsNames) : IProp GF :=
  iprop(∃ (vc stc rv : Loc) (γv : ChanNames),
    "#Hst" ∷ s.[watchableStore, go!"store"] ↦□ st ∗
    "#Hs" ∷ mvcc.isStore st γ.st ∗
    "#Hrv" ∷ st.[store, go!"ReadView"] ↦□
      (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
    "#Hrvkv" ∷ rv.[readView, go!"kv"] ↦□
      (interface.mkOk (go.GoType.PointerType watchableStore.ty) #s : GoInterface) ∗
    "#Hmu" ∷ sync.isRWMutexGuard (mvcc.wsMuAddr s) (mvcc.watchStoreInv s γ) ∗
    "#Hvc" ∷ s.[watchableStore, go!"victimc"] ↦□ vc ∗
    "#Hvcb" ∷ isChanBag (V := Unit) γv vc (fun _ => iprop(True)) ∗
    "#Hstopc" ∷ s.[watchableStore, go!"stopc"] ↦□ stc ∗
    "#Hstop" ∷ mvcc.isStopChan stc ∗
    "#Hfrz" ∷ mvcc.wsFrozenM γ.st ∗
    "%Hwq" ∷ ⌜γ.st.watchQ = true⌝)

instance mvcc.isWatchableStoreD_persistent (s st : Loc) (γ : mvcc.WsNames) :
    Persistent (mvcc.isWatchableStoreD (GF := GF) s st γ) := by
  unfold mvcc.isWatchableStoreD; simp only [named]; infer_instance

/-- **At `cm = false` the drafted predicate is today's** (`newWatchableStore`'s and `New`'s posts
read as today). -/
theorem mvcc.isWatchableStoreD_off (s st : Loc) (γ : mvcc.WsNames) (h : ¬ mvcc.kbCmpM γ.st.kb) :
    mvcc.isWatchableStoreD (GF := GF) s st γ ⊣⊢ mvcc.isWatchableStore s st γ := by
  unfold mvcc.isWatchableStoreD mvcc.isWatchableStore
  rw [show mvcc.wsFrozenM (GF := GF) γ.st = mvcc.crevFrozen γ.st by
    unfold mvcc.wsFrozenM; simp only [h, ↓reduceIte]]
  exact .rfl

/-- **The "no compactor" fact of an off server** (persistent; what it hands to the watch API,
`NewWatchStream.specD`): its store is frozen. A law, so that the server does not unfold
`isWatchableStoreD` (today's `RestorePre` needs the same fact of `isWatchableStore`: its `sorry`
on `crevFrozen E.γ` is this law at `cm = false`). -/
theorem mvcc.isWatchableStoreD_frozen (s st : Loc) (γ : mvcc.WsNames) (h : ¬ mvcc.kbCmpM γ.st.kb) :
    mvcc.isWatchableStoreD (GF := GF) s st γ ⊢ mvcc.crevFrozen γ.st := by
  unfold mvcc.isWatchableStoreD
  iintro ⟨%vc, %stc, %rv, %γv, H⟩
  iNamed H
  iapply (mvcc.wsFrozenM_off γ.st h).1 $$ Hfrz

/-- **The watch-store invariant's new clause** (draft; a conjunct of `watchStoreInv` at the switch):
no watcher is registered, or the store is frozen. `watch` (registration) has the fact from the
stream (`NewWatchStream.specD`); `syncWatchers`' non-empty branch (`Wu ≠ ∅`, so `M ≠ ∅` by `WsOk`)
takes it here instead of from `isWatchableStore`; every other step keeps `M` empty or the fact. -/
def mvcc.wsWatchFrozen (γ : mvcc.WsNames) (σ : mvcc.WsState) : IProp GF :=
  iprop(⌜σ.M = ∅⌝ ∨ mvcc.crevFrozen γ.st)

/-- `newWatchableStore`'s initial state has no watcher. -/
theorem mvcc.wsWatchFrozen_init (γ : mvcc.WsNames) :
    ⊢ mvcc.wsWatchFrozen (GF := GF) γ mvcc.wsInit := by
  unfold mvcc.wsWatchFrozen
  ileft; ipureintro; rfl

/-! ## The closer and the compaction right -/

/-- **The compaction right from the watchable store's closer** (the glue after the caller's last
error return): in compaction mode, the closer's inner `storeCloser` and the authority's half
(`crevRightM`) make the right at `-1` and the fields for good (`compactRight_of_closer`); the
watchable store's own stop channel and waiter are given up with it (a compacting store is never
closed: `Close` would close the inner store). -/
theorem mvcc.compactRight_of_wsCloser (s st : Loc) (kb : Option mvcc.KBReal) (γs : mvcc.StoreNames)
    (h : mvcc.kbCmpM kb) :
    mvcc.wsCloser (GF := GF) s st γs ∗ mvcc.crevRightM kb γs ==∗
      mvcc.compactRight γs (-1) ∗ mvcc.storeStop st γs := by
  unfold mvcc.crevRightM
  simp only [h, ↓reduceIte]
  iintro ⟨Hcl, Hcr⟩
  iunfold mvcc.wsCloser at Hcl
  icases Hcl with ⟨%stc, -, -, -, Hcl⟩
  iapply mvcc.compactRight_of_closer st γs $$ [$Hcl $Hcr]

/-! ## The drafted specs -/

/-- **Draft of `newWatchableStore.spec`** (P3): the post's `isWatchableStore` is `isWatchableStoreD`
(the frozen fact by the mode), and it gains `crevRightM kb γ.st` (the compaction right's half in
compaction mode, `True` otherwise); and (Q1 (a), `M2StorageDraftSupply.lean`) the pre loses
`kbWTSupplyM kb`, which the compaction takes (`store.Compact.specD`). The rest as today. -/
abbrev mvcc.newWatchableStore.specD : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (kb : Option mvcc.KBReal) (γb γl : GName)
    (P : IProp GF) (f : val) (rd0 : GoFunc) (γi : mvcc.IdxNames) (γok γtag : GName),
  mvcc.batchLimitOk cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = kb ∧ γ.idx = γi⌝ →
        mvcc.storeBackend b s γ P) ∗
      mvcc.kbView kb γb 1 (∅ : mvcc.Bucket) ∗ mvcc.kbNoCmp kb γb ∗ mvcc.kbRegRight kb ∗ mvcc.kbWT kb ∗ mvcc.kbWT kb ∗
      mvcc.kbSRM kb ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), mvcc.kbRT kb) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      mvcc.idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 mvcc.Log) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.newWatchableStore)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ (st : Loc) (γ : mvcc.WsNames), ⌜γ.st.bucket = γb ∧ γ.st.leases = γl ∧ γ.st.kb = kb ∧
        γ.st.idx = γi ∧ γ.st.cok = γok ∧ γ.tag = γtag⌝ ∗
      mvcc.isWatchableStoreD s st γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdIs rd s st γ) ∗ mvcc.hookInit γ.st P f ∗ mvcc.watchWriter γ [[], []] ∗
      mvcc.watchToks γ (2 ^ 63 - 3) ∗ ghostMapAuth γ.st.cok 1 (∅ : GMap w64 mvcc.Log) ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - mvcc.nJobRd kb) (),
        mvcc.watchReader s st γ) ∗
      (∃ stc : Loc, s.[watchableStore, go!"stopc"] ↦□ stc ∗ mvcc.stopCloser stc) ∗
      mvcc.storeCloser st γ.st ∗ mvcc.crevRightM kb γ.st ∗
      mvcc.writerFrag γ.st ∗ mvcc.retiredAt γ.st (mvcc.nJobRd kb) ∗
      typedPointsto (mvcc.wsWgAddr s) (zero_val sync.WaitGroup) (DFrac.own 1) }}

/-- **Draft of `New.spec`** (P3): as `newWatchableStore.specD`, the post's `isWatchableStoreD` and
`crevRightM kb γ.st` beside the closer (`wsCloser`, kept: the caller makes the compaction right
only after its last error return, `compactRight_of_wsCloser`); and (Q1 (a)) the pre loses
`kbWTSupplyM kb`. -/
abbrev mvcc.New.specD : Prop :=
  ∀ (lg : Loc) (b le : GoInterface) (cfg : StoreConfig) (kb : Option mvcc.KBReal) (γb γl : GName)
    (P : IProp GF) (f : val) (rd0 : GoFunc) (γi : mvcc.IdxNames) (γok γtag : GName),
  mvcc.batchLimitOk cfg.CompactionBatchLimit' → receiptBound GF ≤ 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ (s : Loc) (γ : mvcc.StoreNames), ⌜γ.bucket = γb ∧ γ.kb = kb ∧ γ.idx = γi⌝ →
        mvcc.storeBackend b s γ P) ∗
      mvcc.kbView kb γb 1 (∅ : mvcc.Bucket) ∗ mvcc.kbNoCmp kb γb ∗ mvcc.kbRegRight kb ∗ mvcc.kbWT kb ∗ mvcc.kbWT kb ∗
      mvcc.kbSRM kb ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), mvcc.kbRT kb) ∗
      lease.lessorRdOf γl ∗ mvcc.isLessor le γl ∗ lease.rdOwn γl rd0 ∗
      mvcc.idxFresh γi ∗ ghostMapAuth γok 1 (∅ : GMap w64 mvcc.Log) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.New)) (Val #lg))
      (Val #b)) (Val #le)) (Val #cfg))
  {{ (s : Loc), RET #(interface.mkOk (go.GoType.PointerType watchableStore.ty) #s);
      ∃ (st : Loc) (γ : mvcc.WsNames), ⌜γ.st.bucket = γb ∧ γ.st.leases = γl ∧ γ.st.kb = kb ∧
        γ.st.idx = γi ∧ γ.st.cok = γok ∧ γ.tag = γtag⌝ ∗
        mvcc.isWatchableStoreD s st γ ∗ (∃ rd : GoFunc, lease.rdOwn γl rd ∗ mvcc.rdIs rd s st γ) ∗ mvcc.hookInit γ.st P f ∗ mvcc.watchWriter γ [[], []] ∗
        mvcc.watchToks γ (2 ^ 63 - 3) ∗ ghostMapAuth γ.st.cok 1 (∅ : GMap w64 mvcc.Log) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - mvcc.nJobRd kb - 2) (),
          mvcc.watchReader s st γ) ∗
        mvcc.wsCloser s st γ.st ∗ mvcc.crevRightM kb γ.st ∗
        mvcc.writerFrag γ.st ∗ mvcc.retiredAt γ.st (mvcc.nJobRd kb) }}

/-- **Draft of `watchableStore.NewWatchStream.spec`** (no watchers in compaction mode): the pre gains
the "no compactor" fact `crevFrozen γ.st` (persistent; an off server's, `isWatchableStoreD_frozen`),
which the stream keeps for `watch`'s registration (the invariant's `wsWatchFrozen`). The rest as
today. -/
abbrev mvcc.watchableStore.NewWatchStream.specD : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (Q : IProp GF) (Ψ : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStoreD s st γ ∗ mvcc.crevFrozen γ.st }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"NewWatchStream")) (Val #()))
  {{ (ws : Loc), RET #(interface.mkOk (go.GoType.PointerType watchStream.ty) #ws);
      ∃ (γo : mvcc.WsStreamNames) (ch : Loc) (γc : mvcc.WatchChanNames),
        mvcc.isWatchStream ws (interface.mkOk (go.GoType.PointerType watchableStore.ty) #s)
          (mvcc.storeWatchParams s st γ) γo ∗
        ws.[watchStream, go!"ch"] ↦□ ch ∗ isChan ch γc.ch WatchResponse ∗
        inv mvcc.watchN (mvcc.watchChanInv γ ch γc) ∗
        mvcc.watchStreamOpen γo ∗ mvcc.watchConsumer γc [] ∗
        ⌜γo.ids = γc.ids ∧ γo.prog = γc.prog ∧ γo.sentl = γc.sentl ∧ γo.rsn = γc.rsn ∧
          γo.regi = γc.regi ∧ 0 < sint.Z γc.ch.chanCap⌝ ∗ savedPropOwn γo.prog DFrac.discard Q ∗
        savedPredOwn γo.rsn DFrac.discard Ψ }}

end draft

end EtcdGrove
end Perennial
