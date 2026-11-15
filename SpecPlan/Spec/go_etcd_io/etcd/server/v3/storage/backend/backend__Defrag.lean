/-
## `(*backend).Defrag()` (`backend.go:490-502` and the defragmentation, `:504-1000`): trusted (names only)

**Users.** The maintenance server's `Defragment` (`server.go:976`, under the apply lock), bootstrap
(`bootstrap.go:323`, `--experimental-bootstrap-defrag-threshold-megabytes`).

**Why it is true.** Blocking: the batch lock (`Pk`), `mu`, `readTx.Lock`; a commit
(`unsafeCommit(true)`: the hooks, the client's commit step); the live database copied into a
temporary one (`defragdb`); on success the old closed (bbolt waits for open read transactions), the
copy synced, closed, renamed over the file (atomic), reopened, the transactions begun again: every
image is unchanged (the file holds the same entries, the last commit's), a crash leaves the old or
the new file, both the last commit's image. Non-blocking: `safeRangeDeleteMu.Lock()` (waits for the
safe-range deleters: deletes from a safe-range bucket hold its read lock, `beDelHeld`), a commit, a
bulk copy from a read transaction, then the same stop-the-world catch-up (safe-range buckets
appended above the last copied key: their puts are above every key, the put rows' premise; others
copied whole; the registry `safeRangeBucketNames` holds only safe-range buckets: the schema's
initialization registers exactly those, `schema/bucket.go:64`: `safeRegOk`, which `New` takes when
non-blocking defragmentation is configured) and swap. Errors before the swap restore the transactions and are returned; failures
after it are `lg.Fatal` (never returns); a panic inside is turned into `lg.Fatal`.

**What it rests on in bbolt (4c) and OsFs** (verify-round A11-completeness F1-F3, S4; second pass:
bbolt's laws now exist):
* **the copy's `Put`s and `CreateBucketIfNotExists`** (`defragdb` `:827/849`,
  `defragdbAndTrackLastKeys` `:905/930`, `catchUpDefrag` `:1012-1026`): their size premises hold of
  entries read from the source transaction by 4c's `Ent.wf` (keys within `maxKeySize`, entries within
  `bboltEntryMax`, carried by `boltTx_wf`/`boltImage_wf`), so a `Put` error is excluded (and with it
  the stuck error path: `tx.Rollback()` at `:816` before `tmptx.Rollback()` at `:805-809` while
  `tmptx` holds `putLoan`s of `tx`'s bytes);
* **`createDefragTmpDB`** (`:512-546`): `os.CreateTemp`'s empty file, 4c's `boltFresh_alloc`
  (its name not durable until the swap); `bolt.Open(tdbp, 0o600, &options)` with `OpenFile`
  returning the one `temp` file: 4c's one-shot `openFileOk`, and on `Open`'s error the lent file
  back for `temp.Close()` and `os.Remove(temp.Name())` (`:536-538`);
* **`finishDefrag`'s swap** (`:565-606`: both closed, the copy synced, `os.Rename(tdbp, dbp)`,
  `bolt.Open(dbp)`) and **`cleanupTmpDB`'s `os.RemoveAll(tdbp)`** (`:553-560`): 4c's `boltRelease`
  takes each closed database's file out of its `boltFile` (the copy's bytes an image of its data,
  synced: `dur = some []`); then **OsFs's `rename`** (still absent from Perennial's OsFs: the one
  remaining gap, `batch-4c.md`, I7 item 6); then `fileHolds_image`/`fileHolds_alloc` for the reopened
  path. A crash between the rename and a directory sync: `Durable.lean`'s `beRevert` (the old file
  may come back, also the last commit's image);
* **`Begin(true)` on the copy after each intermediate commit** (`:839-845`, `:921-927`, `:1004`): its
  error is excluded by `dbBroken_state` with the commit's success. Were it not, the deferred
  `tmptx.Rollback()` would dereference the `nil` transaction it was reassigned to:
  `nonissues/etcd-backend-defrag-rollback-nil-tx.md` (a precondition etcd meets).

**Changes.** New (no old spec): the defragmentation is in scope.

**Margin.** The file's layout (its size) changes; the specs do not state sizes.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`b.Defrag()`**: some error; every image (batch, visible, committed) unchanged. -/
def backend.Defrag.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beOpen γ q }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"Defrag")) (Val #()))
  {{ (err : GoInterface), RET #err; beOpen γ q }}

end spec

end Backend
end EtcdGrove
end Perennial
