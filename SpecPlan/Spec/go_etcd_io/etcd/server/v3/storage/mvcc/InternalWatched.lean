/-
# A store wrapped by a watchable store (integration Y: I6's G1)

Imported by mvcc's own spec files only (3f's `newWatchableStore`, `watchableStore.Restore`,
`watchableStore.Close`).

## The problem (I6's G1)

The watchable store's sync loop reads the storage directly (`syncWatchers`: `revMu.RLock`, `s.b`,
`ReadTx().RLock`, `UnsafeRange`, under the watchable store's `s.mu`), with one of the store's own
reader slots (`mvccOwnN`). `store.Restore` swaps the storage (`s.b = b`, under the store's own `mu`
only) and gives the old storage's slots back (`storageRest B mvccReaderN`): it is safe only because
the watchable store's `Restore` holds the watchable store's `s.mu`, so no pass is running. The client
holds the whole restore gate (`mvccRestoreGate γ 1`) between restores, so the gate cannot carry the
loops' slots; and `store.Restore`'s own contract cannot know about a lock of the watchable store.

## The design

The store has two **modes**, fixed when it is made:
* **plain** (`NewStore.spec`): the client gets `isMvcc` of the `*store` handle; the loop slots never
  leave the store's invariant, and `store.Restore`/`store.Close` (the contracts at `*store`) use them
  there.
* **watched** (`NewStore.watched.spec`, the instance `newWatchableStore` uses): no `isMvcc` of the
  `*store` handle is ever given for `γ` (so the `*store` instances of the `Restore`/`Close` contracts
  hold vacuously there: their premise names that handle); instead `storeWatched s γ` (persistent,
  with `isStore s γ`) and the loops' shares `storeLoops s γ mvccLoopN`, which the watchable store
  **parks under its `s.mu`** between passes (its `wsMu` holds the park's key), lends one to a pass of
  a loop, and gives all to `store.Restore` through its watched instance (`store.Restore.watched.spec`)
  while it holds `s.mu`, and to `store.Close.watched.spec` after waiting for both loops (each deposits
  its loop share `wsLoopS`/`wsLoopV`, which a pass needs, at `Done`: no pass can then run).

So **`Restore` waits for the loops** (a pass holds `s.mu`, which the watchable store's `Restore`
takes), and the loops' slots are outside the gate: `New`/`newWatchableStore` are provable from
`NewStore.watched.spec`, which `NewStore`'s body proves alongside `NewStore.spec` (the mode is a ghost
choice at the allocation of the store's invariant).

## Vocabulary

* `mvccLoopN` (named, `2`): the loop shares, part of `mvccOwnN`.
* `storeWatched s γ` (persistent): `s` is the inner store of a watchable store (watched mode).
* `storeLoops s γ n` (exclusive, counted): `n` loop shares: each a reader slot of the store's
  **current** storage and one of `revMu`, with read access to the field `s.b` (Restore writes it only
  with every share in hand). Intended realization: a fragment of the store's ghost count of shares
  out; the store's invariant holds `kbRdToks B (mvccLoopN - out)` of its current storage `B` and the
  matching `revMu` slots; a share converts to the slots of the storage current at the conversion
  (3f's `wsReadAt` holds them for the pass).

## Laws

`storeLoops_split`, `storeWatched_persistent`, `storeWatched_isStore`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Internal
public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel go_etcd_io.etcd.server.v3.storage.mvcc

/-- **A watchable store's loop shares** (named): one per sync loop. -/
def mvccLoopN : Nat := 2

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **`s` is the inner store of a watchable store** (persistent): watched mode (see the header). -/
opaque storeWatched [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : MvccName) : IProp GF := iprop(True)

/-- **`n` of the store's loop shares** (exclusive, counted; see the header). -/
opaque storeLoops [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (s : Loc) (γ : MvccName) (n : Nat) : IProp GF := iprop(True)

end vocab

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

def storeLoops_split.spec : Prop := ∀ s γ n m,
  storeLoops (GF := GF) s γ (n + m) ⊣⊢ storeLoops s γ n ∗ storeLoops s γ m

def storeWatched_persistent.spec : Prop := ∀ s γ, Persistent (storeWatched (GF := GF) s γ)

def storeWatched_isStore.spec : Prop := ∀ s γ, storeWatched (GF := GF) s γ ⊢ isStore s γ

end laws

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`NewStore`, the watched instance** (what `newWatchableStore` calls): `NewStore.spec`'s
triple, the store made in watched mode: `storeWatched s γ` and the loops' shares in place of
`isMvcc` of the `*store` handle (proved by `NewStore`'s body with the other choice of mode). -/
def NewStore.watched.spec : Prop :=
  ∀ [ReceiptBoundLe GF (2 ^ 48)] (lg : Loc) (le : Loc) (cfg : StoreConfig) (B : MvccStorage)
    (Pk : IProp GF) (h : EtcdModel.KVHist) (u : Bool) (γl : Lease.Names) (c : Lease.Cfg) (n : Nat)
    (ls : Lease.LessorState) (dq : DFrac) (f : GoFunc) (Pre Q' Post X Y : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ ⌜storeCfgOk cfg⌝ ∗
      mvccStorageFor B Pk h u ∗
      storageHook B dq f ∗ ⌜f = func.nil ∨ dq = DFrac.discard⌝ ∗
      Pre ∗ hookRun B Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗ X ∗ storageReq B Pk X Y ∗
      Lease.isLessor le γl c ∗ Lease.lessorState γl n ls }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.NewStore)) (Val #lg))
      (Val #(GoInterface.ok (storageVal B)))) (Val #(Lease.lessorIface le))) (Val #cfg))
  {{ (s : Loc), RET #s; ∃ γ : MvccName,
      storeWatched s γ ∗ storeLoops s γ mvccLoopN ∗ mvccLessorIs γ γl ∗
      mvccState γ ⟨h, []⟩ ∗ mvccOpen γ ∗ mvccBackend γ 1 B Pk ∗ mvccReaders γ mvccTokN ∗
      mvccRevLent γ false ∗ mvccRestoreGate γ 1 ∗
      storageHook B dq f ∗ (if u then iprop(Post ∗ Y) else iprop(Pre ∗ X)) ∗
      ∃ (rd : GoFunc) (n' : Nat) (ls' : Lease.LessorState), mvccDeleter rd γ ∗
        ⌜RestoreLs { ls with rd := rd } h.store ls'⌝ ∗ Lease.lessorState γl n' ls' }}

/-- **`store.Restore`, the watched instance** (what `watchableStore.Restore` calls, holding its
`s.mu`): `KV.Restore.contract`'s triple at the inner store, with `storeWatched` in place of `isMvcc`
of the handle and every loop share taken and given back (no pass runs: the shares are swapped to
the new storage, the old storage's slots among `storageRest B mvccReaderN`). -/
def store.Restore.watched.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName) (γl : Lease.Names) (B B' : MvccStorage) (Pk Pk' : IProp GF) (σ' : MvccState)
    (u : Bool) (n : Nat) (ls : Lease.LessorState) (dq : DFrac) (f : GoFunc) (Pre Q' Post X Y : IProp GF)
    (Q : MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      storeWatched s γ ∗ storeLoops s γ mvccLoopN ∗ mvccLessorIs γ γl ∗ mvccOpen γ ∗
      mvccRestoreGate γ 1 ∗ mvccBackend γ 1 B Pk ∗ mvccStorageFor B' Pk' σ'.kv u ∗
      ⌜σ'.pending = []⌝ ∗
      storageHook B' dq f ∗ ⌜f = func.nil ∨ dq = DFrac.discard⌝ ∗
      Pre ∗ hookRun B' Pk' f Pre Q' ∗ (Q' ={⊤}=∗ Pk' ∗ Post) ∗ X ∗ storageReq B' Pk' X Y ∗
      Lease.lessorState γl n ls ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ ∗
              ⌜σ.kv.revs <+: σ'.kv.revs ∧ σ.kv.compacted ≤ σ'.kv.compacted⌝ }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState γ σ' ∗ ⧖ (evCount σ'.kv), COMM Q σ }> }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Restore"))
      (Val #(GoInterface.ok (storageVal B'))))
  {{ RET #(GoInterface.nil); storeLoops s γ mvccLoopN ∗ mvccOpen γ ∗ mvccRestoreGate γ 1 ∗
      mvccBackend γ 1 B' Pk' ∗ storageRest B mvccReaderN ∗
      storageHook B' dq f ∗ (if u then iprop(Post ∗ Y) else iprop(Pre ∗ X)) ∗
      (∃ (n' : Nat) (ls' : Lease.LessorState), ⌜RestoreLs ls σ'.kv.store ls'⌝ ∗
        Lease.lessorState γl n' ls') ∗ ∃ σ : MvccState, Q σ }}

/-- **`store.Close`, the watched instance** (what `watchableStore.Close` calls once both loops have
exited): `KV.Close.contract`'s triple at the inner store, the loop shares back into the store (so
`mvccClosed_rest` gives their slots with the rest). -/
def store.Close.watched.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      storeWatched s γ ∗ storeLoops s γ mvccLoopN ∗ mvccOpen γ }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Close")) (Val #()))
  {{ RET #(GoInterface.nil); mvccClosed γ }}

end spec

end Mvcc
end EtcdGrove
end Perennial
