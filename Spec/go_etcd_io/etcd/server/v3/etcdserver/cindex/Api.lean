/-
# `etcdserver/cindex`: the consistent index (batch 2d): the vocabulary

The consistent index is the index of the last raft entry whose effects are in the backend: etcd
keeps it in memory (`consistentIndex`, `term`), writes it into every backend commit (the backend's
pre-commit hook calls `UnsafeSave(tx)`), and reads it back from the backend when the in-memory value
is `0` (after `NewConsistentIndex` or `SetBackend`). The applying index (`applyingIndex`,
`applyingTerm`) is the entry the apply thread is applying; the post-lock hook of the apply's write
transactions copies it into the consistent index inside the transaction
(`getTxPostLockInsideApplyHook`, `server.go:2478`).

## Users (the pinned etcd)

* the apply thread (`server.go`): `apply` reads `ConsistentIndex()` and sets the applying index of
  each entry it applies past it; `applyEntryNormal`/`applyConfChange` move the consistent index when
  no write transaction did; `snapshot` checks it (`verifyConsistentIndexIsLatest`);
  `applySnapshot` points it at the new backend (`SetBackend`) and reads it back;
* the post-lock hook (`server.go:2478-2484`): `ConsistentApplyingIndex`, `UnsafeConsistentIndex`,
  `SetConsistentIndex`, run by the apply thread while it holds the batch transaction's lock;
* the backend's pre-commit hook (`storage/hooks.go:46`, the backend's commit goroutine, under the
  batch transaction's lock): `UnsafeSave(tx)`;
* bootstrap (`bootstrap.go:257, 273, 491, 629`): `NewConsistentIndex(nil)`, `SetBackend`,
  `ConsistentIndex()` (batch 2e);
* the applier's `Authenticate` (`apply/backend.go:158`, batch 3a): `ConsistentIndex()`.

Snippets: `examples/specreq/cindex/cindex.go` (`ReqApplyMovesIndex`, `ReqReloadAfterSetBackend`,
`ReqSaveInCommit`).

## Vocabulary

* `CIState` (transparent): the in-memory consistent index and term, the applying index and term,
  and the backend the indexer reads from.
* `isCI ci γ` (persistent): `ci` is a `*consistentIndex` with names `γ`.
* `ciState γ m` (exclusive, timeless): **its state is `m`**. Client-owned (TaDa): every method is
  logically atomic over it. The server keeps it in the apply thread's state and in the backend's
  batch-transaction lock invariant (so that the pre-commit hook's `UnsafeSave` reads it: the index
  written with a commit is the last entry whose effects that commit holds).
* `ciWriter γ` (exclusive): the single writer's token (the apply thread's).
* `ciIface l` (transparent): `l` as a `ConsistentIndexer` interface value.
* The backend side (provisional, batch 4a/4b's vocabulary, `req/go_etcd_io_etcd_server_v3_storage_
  backend.md`): `beStoredCI be v` (persistent), "a read of backend `be`'s consistent index (the
  meta bucket, through `be.ReadTx()`, `schema.ReadConsistentIndex`) returns `v` while no commit
  writes it"; and `txStoredCI tx v` (exclusive), the same of the write transaction `tx`'s view,
  which `schema.UnsafeUpdateConsistentIndex(tx, ...)` moves.

## Intended realization

`isCI ci γ`: a lock invariant for `mutex` over `be`; the atomics `consistentIndex`, `term`,
`applyingIndex`, `applyingTerm` in an invariant with `ciState γ m`'s authority (a ghost var of `m`,
`ciState` its client half); the store of `consistentIndex` (or of `applyingIndex`) is the
linearization point of a write, its load that of a read; `ciWriter γ` a ghost var's half whose other
half the invariant holds, required to change `idx`, `be` or `stored`.
-/
module

public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.cindex

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cindex

open Iris Iris.BI

/-- The consistent indexer's ghost names. -/
opaque CINames : Type := Unit

section model
variable [GooseExts]

/-- **The consistent indexer's state**: the in-memory consistent index (`0`: not loaded yet, the
next `ConsistentIndex()` reads the backend), the applying index, the backend it reads from, and what
that backend's stored index is (`none`: no backend to read, `NewConsistentIndex(nil)`). The terms
stored beside the indices are not modelled: Go keeps each pair in two atomics, so a concurrent reader
may see a mixed pair (the specs' margin). -/
structure CIState where
  idx : w64
  aIdx : w64
  be : GoInterface
  stored : Option w64

end model

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

/-- `ci` is a `*consistentIndex` with names `γ`. Persistent. -/
opaque isCI (ci : Loc) (γ : CINames) : IProp GF := iprop(True)

/-- **The indexer's state is `m`**: exclusive, client-owned. -/
opaque ciState (γ : CINames) (m : CIState) : IProp GF := iprop(True)

/-- **The single writer's token** (exclusive): every method that writes the in-memory index
(`ConsistentIndex`/`UnsafeConsistentIndex` when they load it, the setters, `SetBackend`) takes it,
so that a load and the store after it see no other writer (etcd's apply thread is the only writer). -/
opaque ciWriter (γ : CINames) : IProp GF := iprop(True)

/-- (provisional, 4a/4b's) **Backend `be`'s stored consistent index is `v`** (`0`: none), as long
as no commit writes it: reads through `be.ReadTx()` (`schema.ReadConsistentIndex`) return it.
Persistent: a commit writes the index only from an indexer whose in-memory index is not `0`, and
the indexer reads the backend only while it is `0`. -/
opaque beStoredCI (be : GoInterface) (v : w64) : IProp GF := iprop(True)

/-- (provisional, 4a/4b's) Write transaction `tx`'s view of the stored consistent index is `v`.
Exclusive (whoever holds the transaction's lock: the pre-commit hook). -/
opaque txStoredCI (tx : GoInterface) (v : w64) : IProp GF := iprop(True)

/-- `l` as a `ConsistentIndexer`. -/
def ciIface (l : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty)
    #l

end vocab

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

def isCI_persistent.spec : Prop := ∀ ci γ, Persistent (isCI (GF := GF) ci γ)

def ciState_timeless.spec : Prop := ∀ γ m, Timeless (ciState (GF := GF) γ m)

def ciWriter_excl.spec : Prop := ∀ γ, ciWriter (GF := GF) γ ∗ ciWriter γ ⊢ iprop(False)

def beStoredCI_persistent.spec : Prop := ∀ be v, Persistent (beStoredCI (GF := GF) be v)

def ciState_excl.spec : Prop :=
  ∀ γ (m m' : CIState), ciState (GF := GF) γ m ∗ ciState γ m' ⊢ iprop(False)

end laws

end Cindex
end EtcdGrove
end Perennial
