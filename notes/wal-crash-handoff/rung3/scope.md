# Crash ladder, rung 3: the backend and consistent-index replay under power loss (Scope)

2026-11-11, for etcd-grove-81. Design only. Nothing in any worktree was edited, built or committed;
nothing was pushed. Go experiments under `/shared/tmp/crash-rung3/go/` (module `crashrung3`).

Pins and abbreviations:
- **B/** = `/root/go/pkg/mod/github.com/upamanyus/bbolt@v0.0.0-20261104031046-743299d8cec8`: bbolt as
  `etc/goose.py`'s project `bbolt` pins it (fork `743299d8`, etcd's v1.5.0 plus the fork's fixes) and as
  `examples/go.mod` replaces it.
- **S/** = `/root/go/pkg/mod/github.com/upamanyus/etcd/server/v3@v3.0.0-20261103162249-673da07c8fab`
  (etcd at the pin `673da07c8f`). WAL W3's pin move (`goose-lean-walsync` `71f99a4bf`, worktree
  `/shared/etcd-grove-walw3`) touches only the WAL and `TouchDirAll`: nothing below changes.
- Lean citations are at `lean` `47d7b2f2cd`.
- **PL** = `/shared/tmp/restart-scope/crash-design-powerloss.md`; P1-P8 are its assumptions (the user
  approved P1, P2 as fsync(2), P4 in its "synced bytes survive a sector rewrite" form, P5, and P7).

## 0. Summary

1. **bbolt's power-loss image at the pin is "the last returned commit, or the one in flight"**, as PL
   §1.3 said (§1), *for a sequence of power losses*. 8,000 crash images of a random commit workload
   (posix, ordered and kill models, chains of up to 5 incarnations) all opened to one of those two
   states and passed `tx.Check` and a post-recovery stress (experiment A, §5).
2. **New candidate bug in bbolt (hard stop: a soundness finding against PL's P7 claim).** A *process
   kill* (kill -9, OOM, a panic of another goroutine) between a commit's meta `pwrite` and its
   `fdatasync`, a restart without a reboot, then a **power loss** before the restart's first commit
   has synced, **corrupts the database**: the restart opens the unsynced meta from the page cache and
   reuses pages that only the older, durable meta still references; the power loss reverts to that
   meta over the overwritten pages. Reproduced under ptrace in 10 of 1,160 images (posix and the
   ext4-like ordered model alike: `tx.Check` failures, "invalid freelist page" and "page expected to
   be N" panics); **0 of 1,160** with the candidate fix (`Open` fdatasyncs the file before returning)
   (experiment B, §1.6). Upstream main (`etcd-io/bbolt` `622eada1`, 2026-11-11) has the same `Open`.
   So PL §0.1 ("power loss subsumes kill -9: every kill -9 image is a power-loss image") is true of
   one crash but **false of sequences**: a kill's image is not durable. The WAL had the same gap and
   W3's F-Z closes it incidentally (`ReadAll` now fdatasyncs the tail file); bbolt has no such sync.
3. **The consistent index makes the backend's image a log prefix** (§3): every bbolt commit carries
   the current consistent index `ci` in the same transaction (the pre-commit hook), and the apply
   thread's writes for entries `≤ ci` are all in it and none above (`stOk`, `commit_save_au`, proved).
   Replay from the WAL snapshot index with etcd's skip rule (v3 only above `ci`) then reaches the right
   state, including when `ci` is above the WAL's commit (a follower applies before persisting).
   Checked end to end over the real backend, cindex hooks and mvcc store in experiment C (§5):
   **0 violations in 7,200 images**, among them images whose `ci` is above the last returned commit
   (the in-flight one) and images where the backend is ahead of the local WAL mark.
4. **The repo today has no crash statement about real bbolt or the backend** (§2): the server's bbolt
   is an axiomatized key-value contract (`InvBbolt.lean`), and `fileHolds` is explicitly the page
   cache; mvcc's B3 relates a *stopped* backend's data to the store (`mvccImage_stop.law`); the restart
   image is graceful-only (`InvRestart.lean`). The proposal adds a client-owned durable ghost
   `boltDisk path ⟨last, flight⟩`, a trusted crash relation `boltImg`, and two atomic updates to
   `Tx.Commit_kv` (at the call, and at the meta's `fdatasync`); everything above bbolt is proved from it
   (§2.3).
5. **Tester and theorem** (§4): a new example `examples/etcd/mvcccrash`, one member, the
   `etcd_wal_safe` pattern: a per-incarnation `Boot` re-run after every crash under Perennial's
   `goose_crash_adequacy`, the image given only by the crash relation (a separate incarnation, not an
   in-process abandoned one: §4.3). Theorems `etcd_mvcccrash_adequate` / `etcd_mvcccrash_safe`.
6. **Stages** (§6): ≈ 10-16 weeks; Go part done in prototype here. Decisions: the bbolt fix (user),
   the extension shared with WAL W4/C6, the tester's scope (81).

## 1. bbolt under power loss at the pin

### 1.1 The commit (`Tx.Commit`, B/`tx.go:171-283`)

In order, for a read-write transaction:
1. `rebalance`, `spill` (`:197-212`): the dirty nodes become dirty pages, allocated from the freelist
   or at the end of the file. Copy-on-write: a page reachable from the current meta `N` is never
   rewritten; the spilled nodes go to new pages.
2. The old freelist page is freed under this transaction's id (`:218-220`), and with
   `NoFreelistSync = false` (etcd's setting, PL §1.3) a new freelist is written to newly allocated
   pages (`commitFreelist`, `:286-300`). The freelist written holds the free *and pending* ids.
3. If the high-water mark grew, `db.grow` (`db.go:1296-1334`): `ftruncate` to the new size, then
   `File.Sync` (fsync), unless `NoGrowSync` (etcd: false). So the size is durable before any page
   beyond the old end is written.
4. `tx.write()` (`tx.go:526-597`): every dirty page, sorted by id, by `pwrite` (`db.ops.writeAt =
   db.file.WriteAt`, `db.go:269`), then **`fdatasync`** (`:572-578`, `bolt_linux.go:8`).
5. `tx.writeMeta()` (`:601-630`): the meta is serialized into a fresh page-sized buffer, with
   `p.id = txid % 2` (`internal/common/meta.go:54`) and the FNV-64a checksum (`meta.go:58, 63-68`),
   written by one `pwrite` at page `txid % 2`, then **`fdatasync`** (`:619-625`).
6. `tx.close()`, the commit handlers.

An error at step 4 or 5 rolls back in memory and returns it. An error in step 5's `fdatasync`, or after
its `pwrite`, may still have made the meta durable: the commit returned an error but may survive a
crash. etcd treats any commit error as fatal (`batchTx.commit`, S/`storage/backend/batch_tx.go:291, 301-303`:
`Fatal`), so the process stops with the image either `N` or `N+1`.

### 1.2 Open (B/`db.go:182-340`)

- `os.OpenFile(path, O_RDWR|O_CREATE)` (`:241`), `flock` exclusive (`:252`). **No directory fsync** of
  the parent after a create: the file's entry is durable only if someone fsyncs the directory (P2;
  §1.5).
- A zero-length file or zero metas (`metasZero`, `:748-766`) is (re)initialized by the fork's
  crash-safe `init` (`:686-747`: pages 2-3 written and synced, then both metas, synced;
  `nonissues/bbolt-init-not-crash-safe.md`).
- Otherwise `getPageSize` (`:343-446`; the fork's D18: a read error is returned rather than probing on).
- `mmapUnlocked` (`:499-593`): file size (`:477-489`, at least two pages), map, `meta0`/`meta1`
  (`:579-580`), validate both; **error only if both are invalid** (`:584-590`).
- `db.meta()` (`:1214-1236`): the valid meta with the higher txid, else the other valid one.
- `loadFreelist` (`:448-471`): the freelist page of the chosen meta (etcd syncs it).
- In write mode with no synced freelist, `Open` commits once (`:318-333`): not etcd's case.
- **`Open` never `fsync`s or `fdatasync`s the file** (outside `init`). §1.6 is about this.

### 1.3 mmap and remap

Reads go through a read-only `mmap` (`MAP_POPULATE` on Linux under etcd's `boltOpenOptions`); writes
never do: every write is a `pwrite`. The kernel's unified page cache makes the `pwrite`s visible to the
map. So the crash behaviour is that of the `pwrite`/`fdatasync`/`ftruncate`/`fsync` sequence above, and
the map plays no part. Remapping (`mmap`, `:491-497`, on growth past the mapped size) happens under
`mmaplock` with the read transactions excluded; it writes nothing.

### 1.4 What `Open` returns on each power-loss image of commit `N+1` (after `N` returned)

| Crash during | Disk image (P1, P4, P5) | Open returns |
|---|---|---|
| steps 1-3, before any `pwrite` | meta `N` synced; maybe a grown size (synced by `grow`'s fsync) | `N` |
| step 4, before its `fdatasync` returns | arbitrary bytes in pages free in `N` (and in the grown tail); both metas untouched | `N` (nothing reachable from meta `N` was written: copy-on-write, the freelist excludes reachable and pending-for-readers pages) |
| step 5, before its `fdatasync` returns | slot `(N+1)%2` holds meta `N-1`, meta `N+1`, or a torn mix; slot `N%2` holds meta `N` (synced, and a different 4 KiB page: no sector shared, P4) | `N` if the slot is old or torn (P5: a torn meta fails FNV-64a), `N+1` if it holds meta `N+1`, whose pages were synced in step 4 |
| after step 5's `fdatasync` | meta `N+1` synced | `N+1` |

Both metas invalid is impossible: the slot not being written is synced and untouched. The `getPageSize`
probe past page 1 needs both metas damaged (`notes/bbolt-spec-decisions.md:352-356`), which a crash
never does. So **`BoltImg` = the last returned commit, or the one in flight**, under P1 (fdatasync),
P4 (unsynced bytes arbitrary, synced bytes untouched by a later write elsewhere), P5 (no FNV-64a
collision) and P2 for the file's own entry. P3 (rename atomicity) is not used: rung 3 has no rename.

### 1.5 The file's directory entry

bbolt creates `db` without fsyncing its directory. Under P2 the file can vanish after any number of
returned commits (PL's C-P2 for `member/snap/db`). Experiment A without the directory fsync shows it
(the posix model drops the unsynced create: "db file missing", 2 of 120 images in the first trial);
with the child fsyncing the directory once after the first `Open` (the F-N shape), none. W3's F-N2
(`TouchDirAll` fsyncs the parent of each directory it creates) does not cover it: the remaining fork
fix for the server is "fsync `member/snap` after bbolt creates `db`" (PL §1.4, C0b). **For rung 3 the
tester is the program, so it fsyncs its own directory after the first `Open`**: no fork change and no
assumption (§4.1).

### 1.6 Candidate bug: a kill, a restart, then a power loss corrupt the database

**Sequence** (at the pin and at upstream main):
1. Commit `F` (txid `t`) has synced its data pages and `pwrite`n its meta into slot `t%2`; the process
   is killed before the meta's `fdatasync` (kill -9, OOM kill, or a `Fatal`/panic elsewhere in the
   process: etcd's raft loop `Fatal`s on WAL errors, any goroutine's panic ends the process).
2. The process restarts without a reboot (systemd). `Open` reads both metas from the page cache: meta
   `F` is valid and newest. **Nothing makes it durable**: the disk may still hold the old slot.
3. `F`'s freelist lists as free the pages `F` freed, which the previous meta `L` (txid `t-1`, slot
   `(t-1)%2`, durable) still references. The restart's first commit `G` allocates some of them and
   `pwrite`s its pages there.
4. Power loss before `G`'s data `fdatasync` (which would also have flushed meta `F`): the kernel may
   have written back `G`'s pages but not meta `F`'s page. The disk now has meta `L` (valid, newest
   valid) whose tree points into pages holding `G`'s data.

**Result**: `Open` succeeds or panics; `tx.Check` reports "multiple references", "reachable freed",
out-of-order keys; reads panic ("page expected to be: 44, but self identifies as …", "invalid freelist
page"). It is a lost database (or silently wrong data), not just a lost commit.

**Evidence** (`TestBoltKillThenPower`, §5): inc 0 makes 10 commits (taken as durable), inc 1 is killed
at the entry of a random `fsync`/`fdatasync` under ptrace (the page cache survives, the process does
not), inc 2 runs in the same directory, and the recorder replays inc 1's and inc 2's writes over inc
0's state as power-loss images. **10 of 1,160 images violate**, every one with inc 2 having opened
`F` and the crash before inc 2's first commit returned, 5 under the posix model and 5 under the
ordered (ext4/xfs) one. With the child calling `db.Sync()` right after `Open` (the candidate fix):
**0 of 1,160**.

**Fix**: `Open` in write mode `fdatasync`s the file before returning (one call, after `mmap`, when the
file was not just initialized). Cheap (one flush per open). Upstream main's `Open` has no sync either
(`db.go` at `622eada1`: its only `fdatasync`s outside commits are `init`'s and `DB.Sync`).

**Known upstream?** Not as such. Unexplained corruption reports with the same signatures after restarts
or hard resets: etcd-io/bbolt#778 (open, "freepages: failed to get all reachable pages … multiple
references" after a process restart), #701 (closed, power-off page cycle), #562 (closed, hard reset;
attributed to ext4 fast_commit). None names this mechanism; I do not claim they are it.

**Reach through etcd**: etcd opens the backend with the same `bolt.Open` (S/`storage/backend/backend.go:
233`), so the same window exists for a member that is restarted after a process crash and then loses
power within its first backend commit. Not tested through etcd's server (the bbolt-level test reaches
the code etcd calls, with etcd's options).

**Status**: a finding to record (CLAUDE.md "Issues in the verified code"): it has a Go test that fails
at the pin and at upstream's `Open`, so `issues/bbolt-open-unsynced-meta-kill-then-power-loss.md` with the
test in `issues/<slug>/` (`/shared/tmp/crash-rung3/go/boltcrash/bolt_test.go`, `TestBoltKillThenPower`;
the ptrace recorder must travel with it, or a gofail-based variant written for upstream:
`beforeSyncMetaPage` is a failpoint in `writeMeta`). `blocks-proof: yes` for any theorem that covers
process kills, no for a power-loss-only theorem.

**What it means for PL**: P7 says a kill -9 is the instance of a power loss whose image is the page
cache. That holds for the *last* crash. A kill followed later by a power loss is not two power losses:
after the kill, the restarted program reads state that is not durable. Any component that, after a
restart, acts on what it read without syncing it can break. The WAL: before W3, `ReadAll` in write mode
did not sync, so a restarted follower could ack entries it read from the page cache (raft sends the
ack without a sync when nothing new is appended); W3's F-Z (`ReadAll` fdatasyncs the zeroed tail)
syncs the tail file, and earlier files were synced at their cut, which closes it for the WAL (not
tested here: a W4 note). bbolt needs its own fix.

### 1.7 Other candidates checked, none found

- Torn meta with valid checksum: P5 (minibolt's P1 precedent, `examples/osfs/bboltfs/README.md:38-43`).
- Grow: the size is synced before pages past the old end are written (§1.1 step 3).
- A commit error after the meta write: may be durable (§1.1); etcd stops on it; the relation keeps the
  in-flight commit possible after an error (§2.3).
- Freelist after recovery: experiment A's stress step (8 more commits, reopen, `Check`) on every image:
  no failure.
- `WriteTo`'s meta parity (D21, fork `e1fae5c`): only for snapshots sent to followers (not rung 3).
- Defragmentation's rename (PL C-P4): out of scope (no defrag in the tester).

## 2. What the models say today, and the proposed crash relation

### 2.1 Today

- **The server's bbolt is a names-only key-value contract** (`Proof/go_etcd_io/etcd/server/v3/storage/
  backend/InvBbolt.lean`, axioms `:100-117`): `ownDB db γ D` (committed data), `ownWTxG tx γ D S G` (the
  write transaction), `rtxSnap tx D`, `fileHolds path D` ("the database file at `path` holds `D`: what
  `bolt.Open` reads"), `dbFile db path`; opaque premises `dbOpenOk`, `dbCloseOk` (`:77, :87`).
  `Tx.Commit_kv.spec` (`Spec/go_etcd_io/bbolt/Tx__Commit_kv.lean:31-36`): success gives `ownDB db γ S`;
  error gives nothing. `Open_kv` takes `fileHolds path D`; `DB.Close_kv` gives it back. No durability
  anywhere.
- **The proved bbolt** (`Proof/go_etcd_io/bbolt/`, the main tree at `743299d8`): `fileHolds`
  (`Inv/FileHolds.lean:75-79`, sealed in `Spec/go_etcd_io/bbolt/Api.lean:239-240`) is over the OsFs
  page cache, "not 'every byte synced': the in-process specs read the page cache, and durability is out
  of scope" (`Api.lean:141-142`). The backend's axioms are not linked to it. No `specCrash` of real
  bbolt; minibolt (`examples/osfs/bboltfs`) has the only closed crash theorem (`bootCrashSafety`,
  `Results.lean:211`, premise P1 in the crash relation, `BootP1.lean:49-58`).
- **The backend** (`InvBackend.lean`, `Model2.lean:108-128`): the session state separates `C` (bbolt
  committed), `S` (the write transaction), `W`/`R` (buffers); clients see only `bViewC`.
  `backend.Close.spec` gives `bStopView … D ∗ (bFile γ path ∗ fileHolds path D ∨ ¬dbCloseOk)`;
  `backend.New.spec` takes `fileHolds cfg.Path' D` (`New.lean:27-47`). Commit specs expose no
  durability (`backend__ForceCommit.lean`, `batchTxBuffered__Commit.lean`).
- **mvcc's B3** (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/EtcdBackend.lean`):
  `mvccImage D L c u` (`:94-95`, `snap.imageOk`, `Api/SnapImage.lean:567-575`) relates bucket data to a
  history `L`, compaction `c`, unfinished-compaction flag `u`; `entsCutAt` (`Api/CutDefs.lean:66-70`)
  already admits a mid-job compaction. `mvccImage_stop.law` (`:291-299`): a *stopped* backend's data is
  the image of the store's state. `etcdStorage_open.law` (`:174-183`) turns `mvccImage` plus the open's
  post into `mvccStorageFor`, which `ImageBridge.newStore_of_storage` (`Api/ImageBridge.lean:106`)
  unpacks for `NewStore.spec` (proved by `NewStoreR.lean:205`). The consistent index is outside the
  image (the hook's two `Meta` keys, `InvStore.lean:101`).
- **The cindex** (`Proof/.../etcdserver/InvCindex.lean`, `CindexBackend.lean`, `InvApply.lean`): the
  hook writes `ci` into every commit (`ci_hook_backend`, `CindexBackend.lean:619`); `stOk`
  (`InvApply.lean:164`) and `commit_save_au` (`:940`): the `ci` a commit reads has nothing in the
  buffer above it and everything at or below it processed.
- **Restart** (`InvRestart.lean`): `srvFiles` (`:79`) = `walFiles ∗ backend.fileHolds`, and
  `srvDiskImage` (`:135`) requires WAL snapshot ≤ backend `ci` ≤ WAL commit; graceful stops only
  (`:15-20`). `RestReplay.lean` (`RestartPt`, `:56`) replays from `b` (the WAL snapshot index) to `A₀`.
- **durableExt** (`GooseLang/Ext/Durable/Impl.lean:56-72`): whole-file atomic; sound under P1-P3 given
  its directory's entry (PL §3). **OsFs** (`GooseLang/Ext/OsFs/Impl.lean:462-482`): `CrashImage`
  (durable bytes kept, dirty/lost arbitrary, size in range), `OsCrash`; power loss at byte level.
- **mvccfull** (`examples/mvccfull/mvccfull.go`; `mvccfull_adequate`,
  `Proof/.../examples/mvccfull/Adequacy.lean:209-269`): two in-process members, clean restarts only
  (`:98`, "no crash"), a hook standing in for the consistent index (`:513-526`, nothing persisted),
  through `goose_adequacy_start_files` (crash-free). `notes/mvccfull.md:120-122`: two injected bugs
  (M1, M7) differ from mvcc only after a crash.

### 2.2 What a crash relation must add

1. A **durable state that survives a crash**, owned by the client (raft's durable-API lesson,
   `notes/bbolt-spec-decisions.md:699-706`: "the client owns the durable state, and the commit point
   after `fdatasync` is an update").
2. **The commit in flight**: between the commit's start and the meta's `fdatasync`, a crash can give
   either state; after an error too.
3. **What a crash gives**: the file holds one of them, and that state is now the durable one.
4. For kill-then-power (§1.6): after a kill the file reads a state that need not be durable until
   something syncs it; with the fixed `Open`, `Open` is that sync.

### 2.3 The proposed spec (trusted part: bbolt only; the rest proved)

**Vocabulary** (new module `Spec/go_etcd_io/bbolt/Durable.lean` or in `InvBbolt.lean`; names are
proposals):

```lean
/-- A bbolt file's durable state: the data of the last commit that returned (or that the last
`Open` made durable), and the commit in flight, if any (begun, its meta maybe written). -/
structure BoltDur where
  last   : Data
  flight : Option Data

/-- **What a power loss can leave of a bbolt file whose durable state is `d`** [trusted text]: the
last returned commit, or the one in flight (§1.4; P1, P4, P5, and the file's entry durable, P2). -/
def boltImg (d : BoltDur) (D : Data) : Prop := D = d.last ∨ d.flight = some D

/-- The client's durable ghost for the file at `path` (sealed; crash-stable: the crash relation
rewrites it). -/
axiom boltDisk (path : GoString) (d : BoltDur) : IProp GF
```

**The crash relation** (the local extension's, §2.4): at a crash, every `boltDisk path d` becomes
`boltDisk path ⟨D, none⟩ ∗ fileHolds path D` for some `D` with `boltImg d D` (power loss). With the
`Open` fix the kill instance is the same relation with the post-crash ghost `⟨d.last, some D⟩` (if
`D ≠ d.last`) until `Open` syncs; without the fix the relation is **only** for power losses and the
theorem says so.

**Today's axioms, extended (conjoined, not replaced)**:
- `Open_kv`: pre adds `boltDisk path d` with `fileHolds path D` and `boltImg d D` (or `D = d.last`);
  post adds `boltDisk path ⟨D, none⟩` (the fixed `Open` syncs; the unfixed one only in the power-loss
  instance, where `d = ⟨D, none⟩` already). A new file: `boltDisk path ⟨∅, none⟩`, given its entry
  durable.
- `Tx.Commit_kv`: two atomic updates, as raft's `Ready`/`Advance` durable API:
  ```
  {{ today's pre ∗ dbFile db path ∗
     AU⟨boltDisk path ⟨D, none⟩⟩ ⟨boltDisk path ⟨D, some S⟩, COMM Q₁⟩ ∗
     (Q₁ -∗ AU⟨boltDisk path ⟨D, some S⟩⟩ ⟨boltDisk path ⟨S, none⟩, COMM Q₂⟩) }}
    tx.Commit()
  {{ RET err; txDone tx ∗ ((err = nil ∗ ownDB db γ S ∗ wrTok γ ∗ Q₂) ∨ (err ≠ nil ∗ Q₁)) }}
  ```
  The first update fires before any `pwrite`, the second at the meta's `fdatasync`. An error leaves the
  flight possible (§1.1). `D` here is `ownDB`'s committed data: the client's invariant ties
  `boltDisk path d` to `ownDB`'s `D` (`d.last = D` while no commit runs).
- `DB.Close_kv`: unchanged (no write in etcd's settings). `fileHolds` keeps its page-cache meaning.

**Proved layers above** (no new trust):
1. **Backend** (`InvBackend.lean`): the backend owns `boltDisk path d` in its invariant with
   `d.last = st.C` and `d.flight` the commit `batchTx.commit` is running. Law for clients:
   `backend.bDisk γB path P` — every state a crash can leave is a *commit point* of the session: the
   data of some batch commit, with the hook's writes in it (`commitReq X Y` already gives the hook its
   window). Clients choose `P`, a predicate the hook re-establishes at each commit.
2. **cindex + mvcc** (`etcdserver/`, `mvcc/`): `P D := ∃ ci, metaIs D ci ∧ mvccImage D (L.upto ci) c u`,
   from `commit_save_au` (nothing above `ci` buffered, everything at or below processed) and a new
   **`mvccImage_commit.law`**: `mvccImage_stop.law` generalized from the stop view to every commit point
   (the B3 argument is about the committed data and the store's state at a moment when the batch's
   writes are complete; `entsCutAt` already covers a compaction mid-job, `u` its resumption).
3. **The image the restart reads**: `srvBackendImg path lo hi` := `∃ D ci, fileHolds path D ∗
   ⌜metaIs D ci ∧ lo ≤ ci ≤ hi ∧ mvccImage D (L.upto ci) c u⌝`, `lo` the `ci` of the last returned
   commit, `hi` the last applying index. This is what the tester checks and what rung 4's `srvDisk`
   backend arm becomes (PL §3, `BoltImg`).

What this does **not** change: every in-process spec (`ownDB`, `rtxSnap`, the backend's views, B3's
`NewStore`/`New` specs, `ImageBridge`): a crash enters only through `boltDisk` and the relation.

### 2.4 How it enters Perennial

The crash relation must act on a state Perennial's crash semantics sees. bbolt here is names-only (its
calls are axioms), so the state is an **abstract disk in a local extension**: physical state a map
`path ↦ BoltDur`, touched only through the axioms' atomic updates, `ExtSemantics.crash` = `boltImg` per
path (power loss), `boltDisk` its points-to. This is PL §3's C6 design ("an extension (local) whose state
is the abstract disk ghost (`srvDisk`) and whose crash relation is `WalImg ∧ BoltImg ∧ SnapImg`, or an
`ExtCrashInterp` for the trusted contracts"), and WAL W4/C6 plans the same for `walDisk`/`walImg`
(`/shared/tmp/wal-spec/scope.md:369-378, 774`). **Recommendation: one local extension for both**, its
state a map from paths to an abstract file (`walHist` or `BoltDur`), built once (by whichever of W4 and
rung 3 gets there first), each arm's relation its own trusted text. No Perennial change:
`goose_crash_adequacy` takes any per-extension crash relation (PL §3).

## 3. The consistent index

### 3.1 How the server stores it

- Keys `Meta/consistent_index`, `Meta/term`, 8-byte big-endian (S/`storage/schema/bucket.go:84, 88`);
  `unsafeUpdateConsistentIndex` (S/`storage/schema/cindex.go:69-95`) never writes 0, never goes down
  unless forced, writes the term only if positive.
- In memory (S/`etcdserver/cindex/cindex.go:55-138`): atomic `consistentIndex`/`term` and
  `applyingIndex`/`applyingTerm`; `ConsistentIndex()` (`:90-100`) reads the backend when 0;
  `UnsafeSave(tx)` (`:117-121`) writes the atomic pair; `SetBackend` (`:123-129`) resets to 0.
- **The hook**: `BackendHooks.OnPreCommitUnsafe` (S/`storage/hooks.go:45-54`) calls `UnsafeSave` (and
  the conf state if dirty); `unsafeCommit` (S/`storage/backend/batch_tx.go:381-401`) runs it first in
  every commit, then bbolt's `Commit` (`:291`). So every bbolt commit carries the `ci` current at that
  commit.
- **Advancing `ci`**: `apply` (S/`etcdserver/server.go:1922-1972`) sets the applying index for an entry
  above `ci` (`:1939-1944`); the post-lock hook (`getTxPostLockInsideApplyHook`, `server.go:2483-2490`)
  copies it into `ci` when the apply's write transaction takes the batch lock; `applyEntryNormal`'s
  deferred `SetConsistentIndex` (`:1976-1985`) covers entries that take no lock.
- Commit cadence: the backend's timer (100 ms default), the batch limit (10000), a delete (commits at
  `Unlock`, `batch_tx.go:328-360`), `ForceCommit`, `Snapshot`, `Close` (`backend.go:377-479`). The mvcc
  compaction's batches commit on their own (they take the lock outside apply: no hook change of `ci`).

### 3.2 How restart replay skips

- Bootstrap: `bootstrapBackend` (S/`etcdserver/bootstrap.go:255-299`) opens the backend with the hooks,
  `ci.SetBackend(be)`, reads `ci` (`:273`); `recoverSnapshot` (`:449-505`): the newest valid WAL snapshot
  record, `RecoverSnapshotBackend` (S/`storage/backend.go:106-118`: keeps the backend if
  `snap.Index ≤ ci`, else opens `<snap>.snap.db`), and an error if `ci ≠ 0 ∧ ci < snap.Index`
  (`:488-499`).
- Raft restarts with `Applied = 0` (`raftConfig`, `bootstrap.go:580-592`), so `RestartNode` starts at
  the storage's snapshot; `ep.appliedi` starts at the snapshot index (`server.go:760, 808-814`), not `ci`.
- Entries in `(snap, ci]` are replayed v2-only (`shouldApplyV3 = ApplyV2storeOnly`, no backend write);
  entries above `ci` apply (`server.go:1939-1944`, `applyEntryNormal` `:2000-2005`). Proved:
  `EtcdServer__apply.lean:91-144` ("no entry's writes are applied twice, and none above `ci` is skipped",
  `:59-63`), `applyEntryNormal`'s no-v3 branch (`:58-70`).
- **The backend ahead of the WAL**: each `Ready` goes to the apply goroutine (`raft.go:239-243`) before
  the raft goroutine's `Save` (`:264`); a follower applies entries committed by the leader in the same
  `Ready` that appends them; the backend commits on its own cadence. So a crash image can have `ci` above
  the WAL's `HardState.Commit` and above its last entry. Safe: only committed entries are applied, and
  after the restart the leader resends `(commit, last]`, which the skip rule turns into v2-only
  replays up to `ci`. `ForceNewCluster` sets `Commit = max(Commit, ci)` (`bootstrap.go:628-640`) for the
  same reason. Today's `srvDiskImage` requires `ci ≤` WAL commit (graceful only); rung 3's image drops
  that conjunct.
- **Snapshot vs `ci`**: etcd's own snapshot commits the backend first (`snapshot`, S/`etcdserver/server.go:2113-2134`, calls `KV().Commit()` first)
  and then saves the WAL snapshot record, so the WAL snapshot index is ≤ a durable `ci` (given the
  relation: the image is at least the last returned commit). A received snapshot's
  `OpenSnapshotBackend` is PL's C-P1/C4 (rename; not rung 3).

### 3.3 What the tester must check (per restart)

1. The backend and the store open (no panic).
2. **`ci` is in range**: `ci_last ≤ ci ≤ a_max`, where `ci_last` is the `ci` of the last commit that
   returned (`ForceCommit` returns; or the incarnation's starting image) and `a_max` the last entry whose
   apply began. (Timer commits are invisible to the program; the bounds are what it can know.)
3. **The image is the log prefix at `ci`**: the store's current revision, compaction revision, and every
   revision from the compaction up equal the model's after entries `1..ci`.
4. **The snapshot index `s` is ≤ `ci`** (etcd's bootstrap error otherwise).
5. **Replay**: from `s+1` with the skip rule to the end of the log, the store equals the model after the
   whole log (and the leader-supplied suffix above the local WAL commit is part of it).
6. The image where `ci` is above the local WAL commit mark is reached (counted: the "backend ahead"
   case), and the image with `ci` above `ci_last` (the in-flight commit).

## 4. The tester and the closed theorem

### 4.1 Program shape (`examples/etcd/mvcccrash`, package `mvcccrash`)

Laid out as WAL W1.5's tester (`/shared/tmp/wal-spec/etcd-wal-tester/etcd/wal`), goose-translatable
(structs of plain values, slices, one map, loops, no closures beyond the hook, no `fmt`), one goroutine
plus the backend's and mvcc's own:

- `Boot(root, seed, nOps)`, run on whatever the crash left, re-run after every crash (`Main` loops):
  1. **Open as the server does** (`bootstrapBackend` + `NewServer`'s store part): `ci :=
     cindex.NewConsistentIndex(nil)`, `hooks := storage.NewBackendHooks(lg, ci)`, `backend.New` with the
     hooks, `ci.SetBackend(be)`, `schema.CreateMetaBucket`, `lease.NewLessor`, `mvcc.New`,
     `be.SetTxPostLockInsideApplyHook(` the server's hook `)`. On the first boot (the oracle says none
     returned before), fsync `root` after the open (§1.5).
  2. **The oracle** (a `durableExt` file, as W1.5's): the log length `n` (entries are a deterministic
     function of `(seed, i)`, so the oracle stores only counts), `ci_last` (written after a `ForceCommit`
     returns: write-after), `a_max` (written before each apply: write-before), the snapshot index `s`, the
     local WAL commit mark `w` (lagging by design). The candidate-set technique of W1.5 is not needed:
     the bounds are intervals.
  3. **Check** 3.3's items 1-4 against a pure model (the mvccfull model's revisions and compaction,
     restricted to the op mix below).
  4. **Replay** `s+1..n` with the skip rule (`i ≤ ci.ConsistentIndex()` → nothing; else
     `SetConsistentApplyingIndex`, the write transaction, the deferred `SetConsistentIndex`): etcd's
     `apply`/`applyEntryNormal` decision, through the cindex and mvcc APIs. Check item 5.
  5. **New entries**: random Put, DeleteRange, Txn (puts outside its delete, mvccfull's restriction),
     Compact (to a revision at most the current, above the last; never 0), no-op; interleaved with
     `ForceCommit` (then `ci_last`), "snapshot" (`ForceCommit`, then `s := ci`), and the local WAL mark;
     random batch interval and limit, small compaction batches.
  6. Graceful close with probability 1/2.
- No leases, watchers, readers or second member in the first version (each a later extension; mvccfull
  covers them in process). No WAL: rungs 1, 2 and 4 own it; here `w` stands for the WAL's commit only so
  that the "backend ahead" case is named and counted.

### 4.2 The theorem

- `etcd_mvcccrash_adequate`: for every execution of `Main root` under Perennial's crash semantics
  (any number of power losses at any step, `Main` re-run after each), with the oracle in `durableExt` and
  the database file's durable state in the local extension of §2.4 (crash relation `boltImg`), no
  incarnation panics. Premises: the trusted bbolt specs as extended (§2.3), `dbOpenOk`/`dbCloseOk`,
  `durableExt`, the existing names-only/trusted specs the backend, cindex and mvcc proofs already rest on.
- `etcd_mvcccrash_safe`: its consequence in the checks' terms: every restart finds `ci` in
  `[ci_last, a_max]`, the store at the log prefix `ci`, `s ≤ ci`, and replay at the whole log.
- Name per the convention (`etcd_wal_safe`, `etcd_txnlin_safe`, `mvccfull_adequate`): **`etcd_mvcccrash_safe`**
  (and `_adequate`), a tcb collection `etc/tcb-collections/mvcccrash.txt`.

### 4.3 How crash images enter the proof: a separate incarnation (recommended) vs. in process

- **In-process abandoned incarnation** (kvdurable's `Cluster.Crash`): the program abandons the member
  and opens a new one on "the image". For bbolt this does not work as Go:
  - the abandoned `*DB` keeps its exclusive `flock` (per open file description), so a second `Open` of
    the same path in the same process blocks forever (`Timeout` 0); a new path per incarnation needs a copy;
  - the abandoned backend's goroutines keep running (the batch timer commits, the compaction), and the
    backend has no stop-without-commit;
  - Go cannot produce the in-flight or torn image in process: a copy under a read transaction gives the
    last commit only, a raw copy is not even a crash image (a later commit can reuse a page the copy has
    not read yet). So the image would come from a trusted test-only primitive whose Go body is not the
    behaviour proved: faithful only by fiat.
- **Separate incarnation** (`Boot` re-run by Perennial's crash semantics; the Go driver re-runs it under
  ptrace on recorded images, as experiments A and C do here and W1.5 did for the WAL): the image comes
  only from the crash relation, the Go tester is exactly the program the theorem is about, and the
  executable check exercises every image the recorder builds.
- **Recommendation: separate incarnation.** It costs the local extension (§2.4), which C6 needs anyway,
  and a crash-stable invariant over the oracle and `boltDisk` (the `kdFileInv` pattern).

## 5. Go validation (done here, before any Lean)

Code: `/shared/tmp/crash-rung3/go/` (`crashsim/` = W0's ptrace recorder with a kill-at-sync option;
`boltcrash/`; `mvcccrash/`). Build and run (as in this report):

```
cd /shared/tmp/crash-rung3/go
GOWORK=off GOFLAGS=-mod=mod GOPROXY=off TMPDIR=/shared/tmp PATH=/usr/local/go/bin:$PATH \
  go test -c -o ../boltcrash.test ./boltcrash && go test -c -o ../mvcccrash.test ./mvcccrash
cd .. && systemd-run --scope -q -p MemoryMax=32G ./boltcrash.test -test.run TestBoltChains -test.v -chains 40 -incs 5 -images 40 -fn
systemd-run --scope -q -p MemoryMax=32G ./boltcrash.test -test.run TestBoltKillThenPower -test.v -chains 30 -images 40 [-opensync]
systemd-run --scope -q -p MemoryMax=32G ./mvcccrash.test -test.run TestMvccCrash -test.v -chains 40 -incs 6 -images 30 -entries 40
```

Logs: `/shared/tmp/crash-rung3/{a1,b1,b1-fix,c1,...}.log`.

| Experiment | What | Images | Result |
|---|---|---|---|
| A (`TestBoltChains -fn`) | bbolt at the pin, etcd's options (array and map freelists), 25 random commits per incarnation (values up to 60 KB: overflow pages, growth), chains of 5 incarnations over the images; each image: `Open`, `Check`, state = last returned or in-flight commit, then 8 more commits, reopen, `Check` | 8,000 (40 chains × 5 incarnations × 40) | **0 violations**; 671 images opened to the in-flight commit |
| A without F-N (first trial) | same, the directory never fsynced | 120 | 2 "db file missing" (posix: the create was not durable; §1.5) |
| B (`TestBoltKillThenPower`) | kill at a random sync, restart in place, power loss (posix/ordered) | 1,160 | **10 violations** (corruption; §1.6) |
| B with `-opensync` | the same with `Open` followed by `db.Sync()` | 1,160 | 0 |
| C (`TestMvccCrash`) | etcd's backend + cindex hooks + mvcc store, 40 entries per incarnation, random batch interval/limit, compaction batches of 2, chains of 6; checks 3.3 1-6 on every image | 7,200 (40 chains × 6 × 30) | **0 violations**; `ci` above the last returned commit in 4,933, backend ahead of the WAL mark in 6,443, db absent before any commit returned in 31 (= the empty state) |
| C without F-N (`-fn=false`) | the directory never fsynced | 1,800 | 66 "db missing" after commits returned (C-P2 at the tester level; §1.5); no other violation |

Notes on the harness: the recorder sees every `pwrite`/`fdatasync`/`fsync`/`ftruncate` under the root
(bbolt writes only by `pwrite`; reads by `mmap` do not matter). The image models are W0's (posix: per
sector new/old/random, size in the synced range, unsynced namespace operations dropped
order-preservingly; ordered: namespace in order; kill: the page cache). P4's garbage mode (random bytes
in an unsynced sector) is not used here; under the approved P4 wording it is only for unsynced sectors,
which the posix mode's per-sector random choice among written versions approximates (see §6, open item).

## 6. Stages, sizes, decisions, overlap

### 6.1 Stages (weeks of work)

| Stage | Content | Size | Checkpoint |
|---|---|---|---|
| R3-0 | Go: the goose-translatable tester (`examples/etcd/mvcccrash` shape, oracle in `durableExt`), the driver over it (W1.5's), a matrix (posix/ordered/kill × seeds; P4 garbage on unsynced sectors only); the bbolt finding as `issues/` with its test; an upstream-shaped gofail test (`beforeSyncMetaPage`) | 1-1.5 | report: matrix, issue draft |
| R3-1 | decisions (below) | — | user and 81 |
| R3-2 | if U-R3-1 = fix: the bbolt fork commit (`Open` fdatasyncs), translation, the proved `Open` re-proved (it has a body: `Proof/go_etcd_io/bbolt/`), pin move (bbolt and bbolt-bank projects), `upstream-report` draft | 0.5-1 | **hard stop before the pin move** |
| R3-3 | trusted text: `BoltDur`, `boltImg`, `boltDisk`, `Open_kv`/`Tx.Commit_kv` extended; Freeze with `spec-reviewer` and the `axiom` skill (sequences with crashes, the error arm) | 1-1.5 | **hard stop: trusted texts** |
| R3-4 | the local crash extension (abstract disk, `boltImg` arm), shared with W4's `walDisk` arm (0.5-1 if W4 builds it first) | 1.5-2.5 | report |
| R3-5 | backend: `boltDisk` in `InvBackend`'s invariant, `bDisk` law (commit points) | 1.5-2.5 | report |
| R3-6 | cindex + mvcc: `mvccImage_commit.law`, `srvBackendImg`, `metaIs` at every commit | 2-3 | report |
| R3-7 | the tester's proof (crash-stable invariant over oracle + `boltDisk`, the replay loop over cindex and mvcc specs, the checks), `etcd_mvcccrash_adequate`/`_safe`, tcb collection | 2.5-4 | **hard stop: closed theorem** |
| **total** | | **≈ 10-16** | |

R3-0 can start at once (Go only, no shared files). R3-3 needs R3-1. R3-4 is the shared piece with W4/C6.

### 6.2 Decisions

**For the user** (world assumptions, scope):

| # | Decision | Recommendation |
|---|---|---|
| U-R3-1 | **Process kills followed by power loss** (§1.6): (a) fix bbolt (`Open` fdatasyncs; fork commit, `issues/` entry, upstream candidate) so the theorem covers kill -9 as P7 intended; or (b) state the theorem for power losses only, and correct PL §0.1 ("power loss subsumes kill -9" holds for one crash, not for a kill followed by a power loss) | **(a)**: one line, real data loss in deployments that restart after a crash, and the theorem then means what P7 says |
| U-R3-2 | No new world assumption: rung 3 uses P1, P2 (fsync(2)), P4, P5 (FNV-64a, minibolt's P1), P6, P7, P8 as approved; P3 is not used | confirm |

**For etcd-grove-81** (design):

| # | Decision | Recommendation |
|---|---|---|
| D-R3-1 | crash entry: separate incarnation vs in-process (§4.3) | separate incarnation |
| D-R3-2 | new example `examples/etcd/mvcccrash`, theorems `etcd_mvcccrash_adequate`/`_safe` (not an mvccfull variant: its `Main` is a two-member in-process program; the tester reuses mvccfull's model and op vocabulary) | yes |
| D-R3-3 | the trusted shape: `boltDisk path ⟨last, flight⟩`, `boltImg`, two atomic updates in `Tx.Commit_kv` (error keeps the flight) | yes |
| D-R3-4 | one local crash extension for WAL and bbolt arms (with W4/C6) | yes |
| D-R3-5 | tester scope v1: one member; Put/DeleteRange/Txn/Compact/no-op; no leases, watchers, readers; the tester fsyncs its directory after the first open (§1.5); `w` a durable field, not the real WAL | yes |
| D-R3-6 | `mvccImage_commit.law` as a generalization of `mvccImage_stop.law` (B3) rather than a new image | yes |

### 6.3 Overlap with work in flight

- **Stage B** (`/shared/etcd-grove-stageB`, grpc, `NewServer` later): no shared files with R3-0..R3-4.
  R3-5/R3-6 touch `InvBackend`, `InvCindex`/`CindexBackend`, `EtcdBackend.lean`, which `NewServer`'s
  proofs import: schedule R3-5/R3-6 after stage B's `NewServer` work lands, or keep their changes
  additive (new laws, the invariant's new conjunct behind the existing sealed names).
- **WAL W3** (`/shared/etcd-grove-walw3`, pin `goose-lean-walsync` `71f99a4bf`): F-Z/F-N1/F-N2 only touch
  the WAL and `TouchDirAll`. R3-0's tester should build against W3's pin once it lands. W3's F-Z also
  closes the WAL analog of §1.6 (tail synced at `ReadAll`): worth a sentence in W4's notes and a
  kill-then-power test in its harness (not run here). The remaining server-side namespace fixes (C-P2:
  fsync `member/snap` after bbolt creates `db`; C-P1: after `OpenSnapshotBackend`'s rename) are rung
  4's, not rung 3's.
- **Restart S3** (`/shared/etcd-grove-rs3`, the raft restart path): disjoint (raft side). Rung 4 joins
  them: S3's restart contract plus rung 3's `srvBackendImg` replace `srvDiskImage`'s
  "`ci ≤` WAL commit" conjunct.
- **WAL W4**: shares the local extension (D-R3-4) and the "crash-stable client ghost + two-update
  commit" pattern; whoever builds the extension first owns it.

### 6.4 Open items

- P4's garbage mode: W1.5 found that garbling a *synced* sector breaks the WAL (§3.3 there) and recommended
  garbage only past the synced offset. bbolt's argument relies on the same wording (a synced meta and the
  synced pages of `N` are not garbled by later writes elsewhere). R3-0's matrix should add a garbage mode
  restricted to unsynced sectors.
- The reach of §1.6 through etcd's server (a member restarted after a process crash): an e2e
  reproduction with gofail (`beforeSyncMetaPage` sleep + kill, restart, then a LazyFS `ClearCache`-style
  drop) would make the upstream report concrete; not needed for the proof.

## Decisions (2026-11-11)
- USER: fork-fix bbolt's Open (a sync/fdatasync after Open trusts the meta), with an issues/ entry (TestBoltKillThenPower) and an upstream candidate; the crash theorems cover kill-then-power-loss sequences. Correct crash-design-powerloss §0.1 ("every kill image is a power-loss image" holds for one crash only).
- USER: confirmed rung 3 needs no new world assumption (P1, P2, P4, P5 incl. bbolt FNV-64a, P6, P7, P8).
- etcd-grove-81: separate incarnation per crash (Perennial crash semantics); new example examples/etcd/mvcccrash (etcd_mvcccrash_adequate/_safe); the bbolt-only trusted shape (boltDisk, boltImg, Commit_kv's two atomic updates), backend/mvcc laws proved; one local crash extension shared with WAL W4/C6; tester v1 one member, no leases/watchers; mvccImage_commit generalizing B3. Schedule the Lean after stage B lands (NewServer imports).
- 2026-11-12 (user): revisit the LinuxFs per-byte model (examples/osfs/bboltfs proved boot crash safety; notes/bbolt-port-plan.md; notes/walfs-ext-plan.md) when rung 3's bbolt Freeze package goes to review: compare boltDisk axioms against it, decide convergence then.
