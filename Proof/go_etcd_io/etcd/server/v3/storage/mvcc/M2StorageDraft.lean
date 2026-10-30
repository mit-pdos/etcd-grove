/-
**M2, the storage side: Draft** (`notes/m2-storage-plan.md`; the backend-cmp Probe's P3, S1-S3,
`notes/spec-first-study/backend-probe.md`; revised after review round 1,
`notes/spec-first-study/m2-storage-review-1.md`). Draft statements and laws only, imported by
nothing but the other Draft modules (`etcdserver/M2StorageDraft.lean`,
`api/v3rpc/M2StorageDraft.lean`, `client/v3/M2StorageDraft.lean`): each `…D` here is what an
existing definition or spec becomes at the switch, written in full so the review reads real Lean;
nothing is switched, nothing assumed (no `axiom`, no `sorry`).

- **P3, the watchable store in compaction mode.** `newWatchableStore` freezes its store's
  compaction revision in every mode today (`crevFrozen_alloc`, kept in `isWatchableStore`'s
  `Hfrz`). Drafted: the frozen fact by the mode (`wsFrozenM`, `True` when the store compacts), and
  the compaction right's half of the revision's authority handed to the caller in compaction mode
  (`crevRightM`, the mode read from the names, as `wsFrozenM`), beside the closer: the caller makes
  the right (`compactRight_of_wsCloser`) only after its last error return (Go's deferred
  `kv.Close()`, `server.go:376-381`), or freezes the store (`crevFrozen_of_new`, any mode) if it
  will watch instead. `newWatchableStore`'s proof needs two changes for it: `crevRight_split` in
  place of `crevFrozen_alloc`, and `isWatchableStoreD` built with its result.
- **No watchers in compaction mode** (M2's round 1; review round 1's F1, the user's decision: a
  client-side premise). The "no compactor" fact is `crevFrozen γ.st` itself (persistent; there is
  none in compaction mode, where the authority's other half is the compaction right's). It travels
  in the client's content of each create request: the store's watch parameters' per-watch token
  becomes `watchTok γ ∗ crevFrozen γ.st` (`storeWatchParamsD`), so `watch` registers a watcher only
  with it, and the watch-store invariant holds `wsWatchFrozen` (no watcher, or the fact), where
  `syncWatchers`' non-empty branch, the only user of `Hfrz`, finds it. gRPC's stream model carries
  a client's contribution to the handler only per request (`Up`), not at the stream's opening, so
  `NewWatchStream` keeps today's text (its stream, over the redefined parameters, takes the fact
  per create); the v3rpc and client statements are in their Draft modules.
- **What reads differently at `cm = false`** (review round 1's S4: the round's header said every
  statement reads as today; false). Today's statements over the redefined `isWatchableStore` and
  `storeWatchParams` read as today's in off mode but for the create token: `watchStream.Watch`'s
  `P.T`, v3rpc's `upOk`/`watchUp` and the client's watch facts gain `crevFrozen` in every mode, so a
  watch client of an off server must present it (from `NewServer.spec`'s post, which gains it). The
  rest (`New`, `newWatchableStore`, `wsFrozenM`, `crevRightM`) reads as today at `cm = false`
  (`wsFrozenM_off`, `crevRightM_off`).
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
mode, so it never changes. A store over mvcc's assumed backend (`kb = none`) counts as compacting
here (`kbCmpM none`): its creator gets the authority's half (`crevRightM`) and chooses, by
`crevFrozen_of_new`, to freeze it and watch (review round 1's S5; `kbCmpM`'s docstring says so at
the switch). -/
def mvcc.wsFrozenM (γs : mvcc.StoreNames) : IProp GF :=
  if mvcc.kbCmpM γs.kb then iprop(True) else mvcc.crevFrozen γs

instance mvcc.wsFrozenM_persistent (γs : mvcc.StoreNames) :
    Persistent (mvcc.wsFrozenM (GF := GF) γs) := by
  unfold mvcc.wsFrozenM; split <;> infer_instance

/-- **The compaction right's half of the revision's authority, by the mode** (draft; a new conjunct
of `newWatchableStore`'s and `New`'s posts; the mode read from the names, as `wsFrozenM`: review
round 1's S3): in compaction mode the caller gets it (and makes the compaction right of it with
the closer, `compactRight_of_wsCloser`, or freezes the store, `crevFrozen_of_new`); otherwise
nothing, the store being frozen. -/
def mvcc.crevRightM (γs : mvcc.StoreNames) : IProp GF :=
  if mvcc.kbCmpM γs.kb then mvcc.crevUB γs.idx (1 : Qp).half (-1) else iprop(True)

/-- At `cm = false` the new conjunct is `True` (the posts read as today). -/
theorem mvcc.crevRightM_off (γs : mvcc.StoreNames) (h : ¬ mvcc.kbCmpM γs.kb) :
    mvcc.crevRightM (GF := GF) γs ⊣⊢ iprop(True) := by
  unfold mvcc.crevRightM; simp only [h, ↓reduceIte]; exact .rfl

/-- At `cm = false` the frozen fact is `crevFrozen`. -/
theorem mvcc.wsFrozenM_off (γs : mvcc.StoreNames) (h : ¬ mvcc.kbCmpM γs.kb) :
    mvcc.wsFrozenM (GF := GF) γs ⊣⊢ mvcc.crevFrozen γs := by
  unfold mvcc.wsFrozenM; simp only [h, ↓reduceIte]; exact .rfl

/-- `newWatchableStore`'s step, by the mode: the authority's half frozen (off) or handed out (on). -/
theorem mvcc.crevRight_split (γs : mvcc.StoreNames) :
    mvcc.crevUB (GF := GF) γs.idx (1 : Qp).half (-1) ⊢
      |={⊤}=> mvcc.wsFrozenM γs ∗ mvcc.crevRightM γs := by
  unfold mvcc.wsFrozenM mvcc.crevRightM
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

/-- **The "no compactor" fact of an off store** (persistent): its store is frozen. A law, so that
the server does not unfold `isWatchableStoreD`: what `NewServer`'s off post hands its watch
clients (`crevFrozen E.γ`, the v3rpc/client Drafts), and what `RestorePre`'s `sorry` on
`crevFrozen E.γ` needs (at `cm = false`; D22's). -/
theorem mvcc.isWatchableStoreD_frozen (s st : Loc) (γ : mvcc.WsNames) (h : ¬ mvcc.kbCmpM γ.st.kb) :
    mvcc.isWatchableStoreD (GF := GF) s st γ ⊢ mvcc.crevFrozen γ.st := by
  unfold mvcc.isWatchableStoreD
  iintro ⟨%vc, %stc, %rv, %γv, H⟩
  iNamed H
  iapply (mvcc.wsFrozenM_off γ.st h).1 $$ Hfrz

/-- **The watchable store's inner store** (review round 1's S2: a law, so the server's glue does not
unfold the predicate; goes to `InvWatchStore.lean` with the redefinition). -/
theorem mvcc.isWatchableStoreD_isStore (s st : Loc) (γ : mvcc.WsNames) :
    mvcc.isWatchableStoreD (GF := GF) s st γ ⊢ mvcc.isStore st γ.st := by
  unfold mvcc.isWatchableStoreD
  iintro ⟨%vc, %stc, %rv, %γv, H⟩
  iNamed H
  iexact Hs

/-- **The inner store's read view, over the watchable store** (S2; as above). -/
theorem mvcc.isWatchableStoreD_readView (s st : Loc) (γ : mvcc.WsNames) :
    mvcc.isWatchableStoreD (GF := GF) s st γ ⊢
      ∃ rv : Loc, st.[store, go!"ReadView"] ↦□
          (interface.mkOk (go.GoType.PointerType readView.ty) #rv : GoInterface) ∗
        mvcc.isReadView rv st γ.st := by
  unfold mvcc.isWatchableStoreD
  iintro ⟨%vc, %stc, %rv, %γv, H⟩
  iNamed H
  iexists rv
  iframe Hrv
  iunfold mvcc.isReadView
  iexists _
  iframe Hrvkv Hs
  iunfold mvcc.kvOver; iright; iexists s; iframe Hst; ipureintro; rfl

/-- **A creator that will not compact freezes the store** (review round 1's S5; any mode): with the
authority's half it was handed (`crevRightM`, in compaction mode, mvcc's assumed backend's
included) or the frozen fact the store already has (off), the "no compactor" fact, so that it can
watch (the create token's, `storeWatchParamsD`). In compaction mode it spends the half: such a
creator gives up compacting. -/
theorem mvcc.crevFrozen_of_new (s st : Loc) (γ : mvcc.WsNames) (E : CoPset) :
    mvcc.isWatchableStoreD (GF := GF) s st γ ∗ mvcc.crevRightM γ.st ={E}=∗ mvcc.crevFrozen γ.st := by
  iintro ⟨#Hws, Hcr⟩
  by_cases h : mvcc.kbCmpM γ.st.kb
  · unfold mvcc.crevRightM
    simp only [h, ↓reduceIte]
    iapply mvcc.crevFrozen_alloc γ.st E $$ Hcr
  · imodintro
    iapply mvcc.isWatchableStoreD_frozen s st γ h $$ Hws

/-- **The watch-store invariant's new clause** (draft; a conjunct of `watchStoreInv` at the switch):
no watcher is registered, or the store is frozen. `watch` (registration) has the fact from the
create token (`storeWatchParamsD`'s `T`); `syncWatchers`' non-empty branch (`Wu ≠ ∅`, so `M ≠ ∅`:
`wsOk_M_ne_of_Wu`) takes it here instead of from `isWatchableStore`; every other step keeps `M`
empty or the fact. -/
def mvcc.wsWatchFrozen (γ : mvcc.WsNames) (σ : mvcc.WsState) : IProp GF :=
  iprop(⌜σ.M = ∅⌝ ∨ mvcc.crevFrozen γ.st)

/-- `newWatchableStore`'s initial state has no watcher. -/
theorem mvcc.wsWatchFrozen_init (γ : mvcc.WsNames) :
    ⊢ mvcc.wsWatchFrozen (GF := GF) γ mvcc.wsInit := by
  unfold mvcc.wsWatchFrozen
  ileft; ipureintro; rfl

/-- **An unsynced watcher has names** (review round 1's open check, `WsOk`): `Wu ≠ ∅` gives `M ≠ ∅`
(an unsynced watcher is live, so it has a state, so names), which is why `wsWatchFrozen`'s
`crevFrozen` is there in `syncWatchers`' non-empty branch. -/
theorem mvcc.wsOk_M_ne_of_Wu (σ : mvcc.WsState) (h : mvcc.WsOk σ) (w : Loc)
    (hw : (σ.Wu !! w).isSome) : σ.M ≠ ∅ := by
  intro hM
  have hl : σ.live w := Or.inr (Or.inl hw)
  have := h.st_m w (h.live_st w hl)
  rw [hM] at this
  simp at this

/-- **The backend's deletable keys fixed at the store's** (review round 1's S2: a law, so the
server's glue does not unfold `storeDlReg`; goes to `InstanceLaws.lean` at the switch). -/
theorem mvcc.storeDlReg_fix (γB : backend.BNames) (γi : mvcc.IdxNames) :
    backend.dlInit (GF := GF) γB ⊢ |==> mvcc.storeDlReg γB γi := by
  iintro H
  unfold mvcc.storeDlReg
  iapply backend.dlReg_fix γB _ $$ H

/-! ## The closer and the compaction right -/

/-- **The compaction right from the watchable store's closer** (the glue after the caller's last
error return): in compaction mode, the closer's inner `storeCloser` and the authority's half
(`crevRightM`) make the right at `-1` and the fields for good (`compactRight_of_closer`); the
watchable store's own stop channel and waiter are given up with it (a compacting store is never
closed: `Close` would close the inner store). -/
theorem mvcc.compactRight_of_wsCloser (s st : Loc) (γs : mvcc.StoreNames) (h : mvcc.kbCmpM γs.kb) :
    mvcc.wsCloser (GF := GF) s st γs ∗ mvcc.crevRightM γs ==∗
      mvcc.compactRight γs (-1) ∗ mvcc.storeStop st γs := by
  unfold mvcc.crevRightM
  simp only [h, ↓reduceIte]
  iintro ⟨Hcl, Hcr⟩
  iunfold mvcc.wsCloser at Hcl
  icases Hcl with ⟨%stc, -, -, -, Hcl⟩
  iapply mvcc.compactRight_of_closer st γs $$ [$Hcl $Hcr]

/-! ## The watch parameters, drafted (F1) -/

/-- **Draft of `storeWatchParams`** (review round 1's F1, the user's: no watchers in compaction mode
as a client-side premise): the per-watch token `T` is the watcher budget's token and the "no
compactor" fact. `watchStream.Watch`'s and `watch`'s `P.T` take it (their texts unchanged), so a
watcher is registered only by a caller that shows the store frozen; v3rpc's create requests
carry it (`upOkD`, `watchUpD`), and the clients present it (`watchMemberFactsD`). The rest as
today. -/
def mvcc.storeWatchParamsD (s st : Loc) (γ : mvcc.WsNames) : mvcc.WatchParams GF where
  IW w := iprop(∃ (γw : mvcc.WatcherNames) (r : mvcc.WatchRange) (fcs : GoSlice),
    mvcc.watcherMeta γ w γw ∗ mvcc.watcherFixed w r fcs ∗ ⌜0 ≤ sint.Z r.startRev ∧ r.id ≠ W64 (-1)⌝ ∗
    ⌜γw.now = false → (γw.lo : Int) ≤ sint.Z r.startRev⌝)
  WC w := iprop(∃ γw : mvcc.WatcherNames, mvcc.watcherMeta γ w γw ∗ mvcc.cancelled γw)
  C _ := iprop(True)
  F f := iprop(∃ p : mvcc.EvM → Bool, mvcc.filterSpec f p)
  CR ch γc L := iprop(isChan ch γc.ch WatchResponse ∗
    inv mvcc.watchN (mvcc.watchChanInv γ ch γc) ∗ ghostVar γc.regl (1 : Qp).half L)
  R := mvcc.watchReader s st γ
  T := iprop(mvcc.watchTok γ ∗ mvcc.crevFrozen γ.st)
  IWF := mvcc.watcherIs γ
  OC w γc := iprop(∃ γw : mvcc.WatcherNames, mvcc.watcherMeta γ w γw ∗ ⌜γw.wc = γc⌝)
  WS w := iprop(∃ γw : mvcc.WatcherNames, mvcc.watcherMeta γ w γw)
  IW_pers _ := by infer_instance
  WC_pers _ := by infer_instance
  C_pers _ := by infer_instance
  F_pers _ := by infer_instance
  IWF_pers _ _ _ _ := by infer_instance
  OC_pers _ _ := by infer_instance
  WS_pers _ := by infer_instance

/-- Only the per-watch token changed. -/
theorem mvcc.storeWatchParamsD_T (s st : Loc) (γ : mvcc.WsNames) :
    (mvcc.storeWatchParamsD (GF := GF) s st γ).T = iprop(mvcc.watchTok γ ∗ mvcc.crevFrozen γ.st) :=
  rfl

theorem mvcc.storeWatchParamsD_R (s st : Loc) (γ : mvcc.WsNames) :
    (mvcc.storeWatchParamsD (GF := GF) s st γ).R = (mvcc.storeWatchParams s st γ).R := rfl

/-! ## The drafted specs -/

/-- **Draft of `newWatchableStore.spec`** (P3): the post's `isWatchableStore` is `isWatchableStoreD`
(the frozen fact by the mode), and it gains `crevRightM γ.st` (the compaction right's half in
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
      mvcc.storeCloser st γ.st ∗ mvcc.crevRightM γ.st ∗
      mvcc.writerFrag γ.st ∗ mvcc.retiredAt γ.st (mvcc.nJobRd kb) ∗
      typedPointsto (mvcc.wsWgAddr s) (zero_val sync.WaitGroup) (DFrac.own 1) }}

/-- **Draft of `New.spec`** (P3): as `newWatchableStore.specD`, the post's `isWatchableStoreD` and
`crevRightM γ.st` beside the closer (`wsCloser`, kept: the caller makes the compaction right
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
        mvcc.wsCloser s st γ.st ∗ mvcc.crevRightM γ.st ∗
        mvcc.writerFrag γ.st ∗ mvcc.retiredAt γ.st (mvcc.nJobRd kb) }}

end draft

end EtcdGrove
end Perennial
