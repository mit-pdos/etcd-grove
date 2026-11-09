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

**Changes (verify-round, A11 F4).** The custom `OpenFile`'s contract is one-shot (`openFileOk`
was persistent, which etcd's defrag closure, returning the one file it created, cannot meet), and
carries the caller's `R`, which an error gives back: bbolt's `db.close()` closed the file
(`db.go:244, 810`), and etcd then closes it again and removes it (`backend.go:536-538`). The
pre's custom disjunct now says the option is non-nil (with `nil`, `Open` calls `os.OpenFile`, and
the contract's `R` would have no source).

**Changes (re-review, N1).** With `NoFreelistSync` off, `Open` ends by committing once, the same
data, to write a freelist page into a file that has none (`db.go:319-334`: any file last written
with `NoFreelistSync`, e.g. etcd's, opened by a tool with the default): a real commit (a new meta
at `txid + 1`, unsynced under `NoSync`; a failed sync marks pages lost), so the client supplies its
updates (`commitAU γ D D o.noSync Sf`, at whatever data `D` the file holds: bbolt instantiates it
from the crash invariant's half of `σ`). The post gives the outcome (`Sf …`) when the commit ran,
or the update back when the file already had a synced freelist (`hasSyncedFreelist`). Without it,
`boltCrash` (a `NoSync` crash leaving the new meta over a lost freelist page) and `boltRelease`
(clean bytes after a failed sync) were false. `OptsM` tracks `noFreelistSync`.
**Proof sketch of that step.** `DB.Begin(true)` on the database just shared (`isBolt`), then
`Tx.Commit.spec` with the instantiated update; on its error `DB.Close` (under the locks) gives
`boltClosed γ` back.

**Margin.** `Open` also reads `Timeout`, `InitialMmapSize`, `FreelistType`,
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
options say, or an error and the file still closed (and, with a custom `OpenFile`, its `R`
back). The options are read and given back. -/
def Open.spec : Prop :=
  ∀ [HasExt osFsExt] [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 62)]
    (γ : BoltName) (mode : w32) (opts : Loc) (dq : DFrac) (o : OptsM) (R : IProp GF)
    (Sf : Bool → Bool → Bool → Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ boltFile γ ∗ boltClosed γ ∗
      optsArg opts dq o ∗ ⌜o.ok⌝ ∗ boltLogger o.logger ∗
      (⌜o.openFile = func.nil⌝ ∨ (⌜o.openFile ≠ func.nil⌝ ∗ openFileOk o.openFile γ.path R)) ∗
      (if o.noFreelistSync then iprop(emp) else iprop(∀ D : Data, commitAU γ D D o.noSync Sf)) }}
    (App (App (App (Val (@! go_etcd_io.bbolt.Open)) (Val #γ.path)) (Val #mode)) (Val #opts))
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err); optsArg opts dq o ∗
      ((⌜err = GoInterface.nil⌝ ∗ isBolt db γ o.noSync ∗ boltOpened db γ ∗
         (if o.noFreelistSync then iprop(emp) else
            iprop(Sf true (!o.noSync) false false ∨ ∀ D : Data, commitAU γ D D o.noSync Sf))) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ boltClosed γ ∗ (⌜o.openFile = func.nil⌝ ∨ R) ∗
         (if o.noFreelistSync then iprop(emp) else
            iprop((∃ ok synced failed brk : Bool, Sf ok synced failed brk) ∨
              ∀ D : Data, commitAU γ D D o.noSync Sf)))) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
