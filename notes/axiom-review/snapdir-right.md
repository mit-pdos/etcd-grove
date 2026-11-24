# The snapshot directory's right, defined (axiom review, 2026-11-23)

**Reviewed** (claim #34, the owner's option (a) for the two opaque world assumptions, via the
coordinator): `snap.Snapshotter.DBFilePath.wp_proof`, `snap.Snapshotter.SaveDBFrom.wp_proof` and
`snap.Snapshotter.ReleaseSnapDBs.wp_proof` (`Proof/.../etcdserver/api/snap/`), with the vocabulary
they take: `snap.isSnapshotter` (`Proof/.../api/snap/Defs.lean`), `snapDirInv`, `snapDir_init`,
`snapDir_take` (`Proof/.../api/rafthttp/Net.lean`), under three candidate definitions:

1. `snapshotterRO` defined (the `fsyncDir` field `↦□ fsyncSnapDir`) and `snap.New` proved, with
   `snapDirIsRO` still opaque (landed: `401414c844`);
2. **the ghost-map form** first proposed for M1: `snapDirIsRO p γd := ∃ γS, (p 0) ↪[γS]□ γd`, so
   `snapDirOwn p` (`∀ γd, |==> snapDirIs p γd`) provable outright;
3. **the file-system form**, adopted: `snapDirOwn p` is the file extension's whole claim on every name
   of the directory `sd` (`p = snapDBPath sd`) but `snap.snapDirNames` (`db` and every index's
   `<16 hex>.snap.db`), with shares of `sd`'s path and call permission; `bootstrapSnapshot` carves it
   (`bootSnap.snapDir_carve`) and `snapDirInv` holds it for good, in place of `snapDirIs`
   (`snapDirIs`/`snapDirIsRO` retired).

Go at the etcd pin `edc800c6f` (`server/etcdserver/api/snap/snapshotter.go:34-72`, `db.go:36-130`).
Not built here: no Goose project, no Lean counterexample (the review ran inside claim #34's worktree,
with no branch of its own); the Go behaviour each attack needs is the one already measured by
`examples/axiomcx/releasesnapdbs` (`TestAttackNames`: non-canonical `.snap.db` entries and empty
directories of such names are removed).

## Verdicts

| definition | `DBFilePath` | `SaveDBFrom` | `ReleaseSnapDBs` |
|---|---|---|---|
| 1. `snapshotterRO` defined, `snapDirIsRO` opaque | survives | survives | survives |
| 2. ghost map, `snapDirOwn` free | survives | weakened (temporary file, below) | **refuted** (paper counterexample) |
| 3. file-system claim in `snapDirInv` (adopted) | survives | survives | survives |

## 1. `snapshotterRO` defined

`isSnapshotter ss sd` is now `fsyncDir ↦□ functions fsyncSnapDir []`, `dir ↦□ sd`, `lg ↦□ lg` with
`zapLoggerOk lg`, and `∃ dd, sd = snapDirOf dd`; `snap.New` gives it (proved). So a program can now
make a snapshotter of any `snapDirOf dd` itself (before, only `bootOk` gave one).

- Go makes a `*Snapshotter` only by `New` (`fsyncDir: fsyncSnapDir`, `lg` never nil) or as the zero
  value from outside the package (`dir = ""`, which is no `snapDirOf dd`: that ends in `snap`).
  Nothing writes the fields after `New`. `SaveDBFrom` calls `s.fsyncDir(s.dir)` on both its success
  paths (`db.go`, the kept file's and the linked file's): the field the predicate now names is the one
  Go calls, where the opaque predicate assumed it silently.
- `DBFilePath` reads only. It takes `fileAt (snapDBPath sd id) D` (an existing file, the claim
  exclusive), so `fileutil.Exist` is true; a relative `sd` cannot carry a claim (the roots are clean
  absolute paths). Its error branch gives `¬ dirReadOk ss`, an opaque fact no law derives the
  opposite of (the closed theorems' premise `storage.snapOpensOk` does, as before: unchanged).
  Cross-world: no entailment from the persistent cells to a pure fact about an opaque function of
  `ss`.
- `SaveDBFrom`, `ReleaseSnapDBs` take `inv snapDirN (snapDirInv sd …)`, which needs the opaque
  `snapDirOwn`: a program's own snapshotter gets nothing further.

## 2. The ghost-map form: `ReleaseSnapDBs` refuted

No ghost name is fixed before the program's proof unless adequacy (or the trusted file extension)
allocates it, and an allocation at a chosen name is not an update of the unit. So the only definable
agreement is under an existential name, `snapDirOwn p` is provable from nothing, and any program may
build `snapDirInv` over a directory of its own. Then:

```go
// d: a fresh root the program owns (dataAreaFresh); sd := d + "/member/snap"
fileutil.TouchDirAll(lg, sd)                       // whole claim on sd's names
// proof: carve snapFreeAll and the claim on "5.snap.db" (BootSnapCarve.carveFree);
//        snapDir_init (snapDirOwn free, Rm := fun _ => True)
s := snap.New(lg, sd)                             // isSnapshotter s sd (proved)
f, err := os.OpenFile(sd+"/5.snap.db", os.O_RDWR|os.O_CREATE, 0600)  // OpenFileS create
if err != nil { return }
f.Close()
s.ReleaseSnapDBs(&raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: 6}})  // Rm j: True
if _, err := os.Stat(sd + "/5.snap.db"); err != nil {
    panic("removed")                               // Go: ENOENT, removed by ReleaseSnapDBs
}
```

The program holds the claim on `5.snap.db`, naming its file, across `ReleaseSnapDBs` by the frame
rule; Go removes the entry (`ParseUint("5", 16, 64) = 5 < 6`), and the `Stat` the proof shows succeeds
fails. The axiom's text excluded this case only by "the environment clause of `snapDirOwn`" (nothing
outside the server's snapshotters writes `.snap.db` files there), which the opaque `snapDirOwn`
carried and a provable one does not. An empty directory named `5.snap.db` gives the same through
`rmdir`. `SaveDBFrom`'s argument for its temporary file ("a name that is no one's claim") fails the
same way: the program may hold the claim on a `tmp*` name.

The other M1 attack, a second invariant over the directory whose `SaveDBFrom` kept-file branch gives
`snapSaved` of an index it does not know, is blocked even here, by `snapFreeAll`: `snapDir_init`
consumes the exclusive claim on every canonical name, and the first invariant keeps holding a share
of the directory's path (in each `fileFree`/`fileAt`) unless all 2^64 indices were saved, so the
directory cannot be replaced to make them again. So the ghost map is not what M1 needs; the
exclusion of the directory's other names is.

## 3. The file-system form (adopted)

The claims of a directory are pairwise disjoint (`Fs.NamesCoh.disj`, the trusted extension's), so
while `snapDirInv` holds `osNames J (.except snapDirNames)` (with a share of `sd`'s path, which fixes
`J`), no one else holds a claim on any name of `sd` but `db` and the canonical ones. Attacks tried:

- **The counterexample of §2.** The program cannot hold `5.snap.db`'s claim and build `snapDirOwn`:
  `.except snapDirNames` and `.only [5.snap.db]` overlap; `.except (5.snap.db :: snapDirNames)` is
  another set, which `osNames_rekey` does not turn into it, and `osNames_merge` needs both. A file
  under such a name made before the carve stays under the invariant's claim (its history `h` is
  free), which no one else can observe; its removal is a step on that claim.
- **An open handle.** A file's descriptor survives the unlink (Linux keeps the inode); the file
  extension has no fd-relative creation (`openat`, `os.Root`; `GooseLang/Ext/Fs/Impl.lean` is
  path-only), so a handle on a removed empty directory cannot be written through.
- **A hard link** of the program's own file into `sd` under such a name needs the claim on the name:
  the invariant's.
- **A second invariant over `sd`** needs the claim again: impossible while the first holds it, now
  with no 2^64 caveat (the right's path share never leaves the invariant).
- **`SaveDBFrom`'s temporary file** (`os.CreateTemp(s.dir, "tmp")`, `O_EXCL`): a `tmp*` name, under
  the invariant's claim alone; concurrent saves get distinct names. Its create, link and remove are
  steps on claims the invariant holds (the canonical name's `fileFree`, the rest's), so the ghost
  steps the docstring states are the code's.
- **The canonical names and `db`**: as before (`snapFreeAll`, `M`, the sealed `snapHeld`; `db` is the
  backend's, never touched by these functions).
- **Restarts** (`bootOkR`, unproved, stage 5): the invariant is the image's, with the claim; a proved
  restart `bootstrapSnapshot` (its `RemoveMatchFile`s of `tmp*`, `*.snap`) will need a law of the
  sealed `snapDirInv` to reach the claim. Not an axiom question.

Not tried: crashes (a power loss leaves `tmp*` files; the next generation's tree, not this
invariant's, is the restart contract's).

## Text changed with it

`snapDirOwn`'s docstring (what it makes true), `snapDirInv`'s, `ReleaseSnapDBs`'s second bullet (the
invariant's claim in place of the environment clause), `SaveDBFrom`'s temporary-file sentence,
`bootOk`'s comment on `Hsdo`, `NewServer.spec`'s comment on the directory.
