/-
`bolt.Open(path, mode, options)` (`db.go`): opens the closed database file of `γ`.

**Users.** `backend.newBackend` (`server/storage/backend/backend.go:233`: etcd's options, a
`*zapBoltLogger`, `MAP_POPULATE`, `NoFreelistSync`, `NoSync = UnsafeNoFsync`), defrag's temporary
database (`backend.go:534`: a custom `OpenFile` returning the file it created, `NoSync`) and its
reopen (`:594`), `examples/bbolt/bank/bbolttest.go:278` (`nil` options), `examples/axiomcx/bboltnan`
(`&bolt.Options{}`). Snippets: `ReqBackendOpen`, `ReqDefrag`, `ReqBank`.

**Proof sketch.** `Open` allocates `db`, reads the options (`optsArg`), opens the file (`os.OpenFile`
over OsFs, or the custom `OpenFile` by `openFileOk`), `flock`s it (trivial in OsFs), and opens
`boltFile γ`'s crash invariant with `boltClosed γ`: the invariant's closed state holds the file's
OsFs halves the open database takes (its `fileHolds`-shaped well-formedness, the other half of `σ`).
A fresh file is laid out by the fork's crash-safe `init` (`nonissues/bbolt-init-not-crash-safe.md`):
each of its steps keeps the invariant's "every crash image is `Data.empty`" (`σ.data = Data.empty`
for a fresh file); else `getPageSize` reads page 0's meta (D18: a read error, not a probe), the file
size, `mmap` (4d's `common` decoders for the metas, `meta()` choosing the newest valid one),
`loadFreelist` (4d's `freelist.Read` of the synced page, else `Init(freepages())`, db.go:454-467;
both on a new freelist, so the hash map's empty-`Init` premise holds trivially). The invariants of `isBolt` (the locks, the
reader pool built from the thread bound, the receipts' counter) are allocated in `γ.ns`. An error
(an errno of OsFs's calls, a closed `flock`, an invalid file: excluded by the invariant) closes the
file again and gives `boltClosed γ` back; the crash invariant never left its closed state, or
returns to it.

**Changes.** The old `Open.spec` took `fileHolds path D` and gave `boltState γ 1 D`, losing the file
on an error and with no crash story. Now the file is named once per generation (`fileHolds_alloc`),
`boltState` is the client's across opens, and an error gives the closed token back. Relaxed: `nil`
options (`DefaultOptions`), a custom `OpenFile` (etcd's defrag, the old round-6 margin), `NoSync`
(a mode). Kept (D13, scope restrictions of the model): read-write, default page size, `Mlock` off,
`MmapFlags` `0`/`MAP_POPULATE`, a pointer-typed logger; the bounds `2 ^ 29` threads and `2 ^ 62`
receipts (owner's bounds, `notes/bounds-plan.md`).

**Margin.** `Open` also reads `Timeout`, `InitialMmapSize`, `FreelistType`, `NoFreelistSync`,
`NoGrowSync`, `PreLoadFreelist`, `MaxBatchSize`, ...: they change no outcome the specs state.
-/
module

public import Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `bolt.Open(γ.path, mode, opts)`: the closed file of `γ` opened as `db`, with `NoSync` as the
options say, or an error and the file still closed. The options are read and given back. -/
def Open.spec : Prop :=
  ∀ [HasExt osFsExt] [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 62)]
    (γ : BoltName) (mode : w32) (opts : Loc) (dq : DFrac) (o : OptsM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ boltFile γ ∗ boltClosed γ ∗
      optsArg opts dq o ∗ ⌜o.ok⌝ ∗ boltLogger o.logger ∗
      (⌜o.openFile = func.nil⌝ ∨ openFileOk o.openFile γ.path) }}
    (App (App (App (Val (@! go_etcd_io.bbolt.Open)) (Val #γ.path)) (Val #mode)) (Val #opts))
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err); optsArg opts dq o ∗
      ((⌜err = GoInterface.nil⌝ ∗ isBolt db γ o.noSync ∗ boltOpened db γ) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ boltClosed γ)) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
