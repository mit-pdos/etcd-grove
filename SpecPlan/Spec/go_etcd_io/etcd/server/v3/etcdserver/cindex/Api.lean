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
  logically atomic over it. The server keeps it in one invariant, which the apply thread (with
  `ciWriter` and an agreement half) and the backend's pre-commit hook (`UnsafeSave`, under the batch
  transaction's lock) both open: the index written with a commit is the last entry whose effects
  that commit holds (round 1, S7).
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

**What cindex gives the backend's pre-commit hook** (verify round, server-boot's request, A8-provability
F5: 4a's `Backend.hookOk γ (hooksIface h) Fh (Pk γ)` at `OpenBackend`): `txStoredCI tx c` is realized
as the write session's view (4a's `beSess γ q Fp.none S`, the batch image) of the `meta` bucket's
`consistent_index` and `term` cells (`c` the stored index, `0` when absent), so `UnsafeSave` under
the hook writes exactly those two cells (`Fh := ciCells`, the cells `schema.UnsafeUpdateConsistentIndex`
puts: 4a's `hookWrites ciCells S S'`), never lowering the stored index (`c ≤ idx`, the `AU`'s
guard); the published update is the indexer's `ciState` (the stored index made visible at the
commit). Server-boot restates `BackendHooks.OnPreCommitUnsafe.spec`/`isHooks` over it.
-/
module

public import SpecPlan.Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.cindex
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Api
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.schema.Api

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

/-- The `meta` bucket's name (schema's `Meta`). -/
def metaBktName : GoString := Schema.Bkt.name .metaB

/-- **The cells the consistent index's save writes** (`schema.UnsafeUpdateConsistentIndex`: `meta`'s
`consistent_index` and `term`): the hook footprint `Fh` of 4a's `hookOk` for the server's
`OnPreCommitUnsafe` (server-boot restates it over this). -/
def ciCells : Backend.Fp := fun c =>
  c = .key metaBktName Schema.ciKey ∨ c = .key metaBktName Schema.termKey

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

/-- `ci` is a `*consistentIndex` with names `γ`. Persistent. -/
opaque isCI [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ci : Loc) (γ : CINames) : IProp GF := iprop(True)

/-- **The indexer's state is `m`**: exclusive, client-owned. -/
opaque ciState [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : CINames) (m : CIState) : IProp GF := iprop(True)

/-- **The single writer's token** (exclusive): every method that writes the in-memory index
(`ConsistentIndex`/`UnsafeConsistentIndex` when they load it, the setters, `SetBackend`) takes it,
so that a load and the store after it see no other writer (etcd's apply thread is the only writer). -/
opaque ciWriter [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γ : CINames) : IProp GF := iprop(True)

/-- (provisional, 4a/4b's) **Backend `be`'s stored consistent index is `v`** (`0`: none), as long
as no commit writes it: reads through `be.ReadTx()` (`schema.ReadConsistentIndex`) return it.
Persistent: a commit writes the index only from an indexer whose in-memory index is not `0`, and
the indexer reads the backend only while it is `0`. -/
opaque beStoredCI [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (be : GoInterface) (v : w64) : IProp GF := iprop(True)

/-- (provisional, 4a/4b's) Write transaction `tx`'s view of the stored consistent index is `v`.
Exclusive (whoever holds the transaction's lock: the pre-commit hook). -/
opaque txStoredCI [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (tx : GoInterface) (v : w64) : IProp GF := iprop(True)

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

/-- **The stored index of a hook's session** (verify round, server-boot's second pass): in a
pre-commit hook's session over 4a's backend `γb` (`beSess γb q Fp.none S`, the transaction
`btIface γb`), the transaction's stored index is the session's `meta` bucket's (`Schema.ciOf`), and
storing `c'` there (`UnsafeSave`) writes only `ciCells`: what 4a's `hookOk` asks of the hook.
Verify round (backend-schema's check): the save's `UnsafePut`s need the batch image's part on the
cells, `beCur γb ciCells C`, which the hook holds (the indexer's invariant, as
`confStateSave_hook`'s `beCur γ confStateCells C`) and gets back updated. -/
def txStoredCI_sess.spec : Prop := ∀ (γb : Backend.BeNames) (q : Qp) (S : Backend.Sess)
    (C : Backend.Image),
  Backend.beSess (GF := GF) γb q Backend.Fp.none S ∗ Backend.beCur γb ciCells C ⊢
    txStoredCI (Backend.btIface γb) (Schema.ciOf (S.cur.ents metaBktName)).1 ∗
    ∀ c' : w64, txStoredCI (Backend.btIface γb) c' -∗
      ∃ (S' : Backend.Sess) (C' : Backend.Image), Backend.beSess γb q ciCells S' ∗
        Backend.beCur γb ciCells C' ∗
        ⌜Backend.hookWrites ciCells S S' ∧ (Schema.ciOf (S'.cur.ents metaBktName)).1 = c'⌝

end laws

end Cindex
end EtcdGrove
end Perennial
