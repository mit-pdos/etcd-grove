# Repair 5: the second crash-story pass (F-server-boot F2-F5, G-a, G-b)

2026-11-09. Inputs:
- `verify/F-server-boot.md` (F2-F5, G-a, G-b), `repair2-crash.md`, `repair3-boot.md`,
  `repair4-raft-crash.md` (F1 is fixed there and not redone);
- `notes/perennial-changes.md`'s crash-frame and OsFs-rename entries;
- the Go: `.lake/src/server` (`bootstrap.go`, `server.go`, `storage/backend.go`, `storage/storage.go`,
  `snap/db.go`), `.lake/src/bbolt`;
- OsFs's crash model (`GooseLang/Ext/OsFs/`, D4: a name is durable only after a directory sync).

The criterion for every law: true of the Go and of OsFs, realizable, not vacuous, and sound at
`L' = L` (`repair4-raft-crash.md`).

## Per finding

### F2: the crash scope enters the logic. Fixed.

**New premise.** `Wal.crashInScope`, an opaque `Prop` in `storage/wal/Api.lean`, declared like
`ServerStorage.diskOk`. It is W0's environment premise: every crash of the run leaves each WAL
directory so that the next `Open` + `ReadAll` returns records meeting `Recs.crashScopeOk`.

**The WAL's crash laws.** `walRecs_crash` and `walWriting_crash` take `crashInScope` and add
`⌜R'.crashScopeOk⌝` to the records they give. This is true under the premise, because `R'` is what
the crash left.

**`disk_crash`** (`ApiBoot.lean`):
- It takes `ServerStorage.diskOk`. This was missing, although its realization applies the WAL laws,
  which take it.
- It takes `Wal.crashInScope`.
- It loses the `crashOutOfScope` disjunct, and `crashOutOfScope` is deleted.

So the adequacy proof needs no case for an out-of-scope crash.

**Checked against the criterion.**
- *Not vacuous.* The premise is false only of a run that has such a crash. That includes the margin
  already recorded: an at-rest crash of a lagging follower with two conf changes above its stored
  commit. A crash can only lower the stored commit, so records that fail `crashScopeOk` at rest
  give `False` there, exactly for such a run.
- *Sound at `L' = L`.* The laws apply only with the crashed generation's `crashed`, so the premise
  is never used of a running generation's records. At `L' = L`, `disk_crash` is still one
  `diskState` consumed and one given, with `crashRest` one-shot per file.

**Threaded to:**
- `disk_crash` (statement);
- `NewServer` (text only, see below);
- `raftNode__start` (text);
- `ReqCrashRecover`'s Assumes and Specs;
- W0's adequacy statement, through the K6 text below.

**`NewServer`: no new premise.** Its triple is a WP and crash-free. No crash law is applied inside
it (the crash frame applies `disk_crash`), and `bootstrap` reads only the restart view `walHolds`.
A `crashInScope` premise there would be an unneeded premise (a hard rule).

### F3: a client address can be served again after a crash. Fixed.

**The change: net/http's protocols are per generation.**

Physically, Perennial's crash is the whole program's machine. Every socket and connection dies, and
nothing is replayed across the crash. So a request that a generation-`L` handler reads was sent by
a generation-`L` `RoundTrip`.

New and changed laws, in `net/http/Api.lean` (trusted):
- **`protoFam a F`** (new; persistent, the run's): the address's family of protocols,
  `F : GooseLocalGS GF → Proto GF`, set once.
- **`reserve`** now reserves a family: `addrFree a ⊢ |==> protoFam a F`.
- **`protoFam_at`** (new): `protoFam a F ⊢ protoAt a (F hG.goose_localGS)`. `protoAt` is now the
  current generation's protocol.
- **`protoFam_gen`** (new): an `⊣⊢` at `L'`.
- **`protoAt_gen`** (repair3-boot) is withdrawn. Kept beside families, it would put two protocols at
  one address in one generation.
- `addrFree_gen` is kept.

Realization: the global set-once map holds saved families, and
`protoAt a P := ∃ F, protoFam a F ∗ ⌜F L = P⌝`. Each connection's byte streams belong to the
generation that made it.

**Users updated:**
- **grpc.** `addrAt` is per generation; its docstring said "for good".
- **2f (rafthttp).**
  - New `raftFam ν`, the family of `raftProto ν` at each generation's heap.
  - `peerAddr` is now over `protoFam`, with `raftCompat` at every generation, so `peerAddr_gen`
    holds by definition.
  - `raftProto_gen` is withdrawn. Nothing needs it now, and the reviewer had questioned its
    realization (second tier).
- **2e (`ApiBoot`).**
  - `cluster_alloc` and `urls_reserve` give `Http.protoFam a (Rafthttp.raftFam ν)`.
  - `srvEp_reserve` reserves a family. The program picks
    `F L := Grpc.grpcOver (etcdContract at ⟨g, L⟩ γ ep) (P L)`, so each generation serves its own
    contract, whose lease rows name that generation's lease views.
  - The header's "Serving clients" paragraph is rewritten.
- **`v3rpc/serve.go`.** The crash claim is fixed: after a crash the address serves the next
  generation's member of the family, through `srvEp_gen`, `Http.protoFam_gen` and `protoFam_at`.

`go vet`-clean.

### F4: `Net.dbIn` names a receiver. Fixed.

Statement changes (`rafthttp/Api.lean`):
- `Net.dbIn : w64 → w64 → IProp GF`: the receiver id, then the index.
- `recvd ν id m` carries `ν.dbIn id s.index`.
- `raftOk ν id`'s `Process` takes `recvd ν id m`.
- `saveOk ν lid sd`'s commit gives `ν.dbIn lid i`.
- `trCfg` passes `saveOk ν tv.ID' sd`.
- `net_alloc` takes the new `DbIn` type.
- `recvChanAt` gains `lid`.
- `newSnapshotHandler.spec` takes `saveOk ν lid sd`.

`EtcdServer.Process.spec` takes `recvd ν (W64 id) m`, the member's own record. Its sketch and
`applySnapshot`'s now name the member's own directory as `snapImage`'s source.

Realization, in `ApiBoot`'s header: `dbIn id i` is a persistent fragment of a per-member history of
saves. It is generation-independent (made at `SaveDBFrom`'s directory fsync, its authority moving
with the directory's invariant across a crash), because `ν` is the same at every generation.

The `snapshot.go` snippet's Assumes is updated.

### F5: `srvEp_agree` from net/http's API. Fixed, narrowed.

**The new trusted law.** `Http.addrFree_protoAt_excl : addrFree a ∗ protoAt a P ⊢ False`. It is
true of the model: `addrFree a` is the exclusive fragment of `a`'s unset key, and `protoAt` at any
generation exists only once `reserve` has set the key. Its realization is a plain entailment, the
fragments' validity.

**2e's `srvEp_reserve`.** It now takes `srvNet γ ν` and is a `|={E}=>` with `↑srvEpN ⊆ E` (new
namespace).
- Its realization opens the cluster's client-address map: an invariant allocated by
  `cluster_alloc`, holding a ghost map `ep ↦ id` and each entry's `protoFam`, with a body over the
  global ghost state only.
- `ep` is not yet in the map: an entry's `protoFam` with `protoFam_at` and the caller's `addrFree`
  give `False` by the new law.
- It then reserves and inserts.

**`srvEp_agree` is narrowed to one cluster.** It gives `id = id'` for one `γ`; it gave `γ = γ'`
too. Only net/http's map is global to the run, and it holds no tag, so cross-cluster agreement is
not realizable. No spec or snippet uses it, and W0's `leaseViewLb γ ep` needs it per `γ` only.

### G-a: a first boot's file after `Close`. Fixed, with a consequence pending the user.

**The fix: a "may vanish" case, recorded in the revert list.**
- **`beOpenUpd`** (4a) also takes `beRevs p os`. When it opens a `none` file (bbolt creates it),
  it gives the list back with `none` added. `none` stays until a directory sync: `SaveDBFrom`'s
  sync of the same directory, `member/snap`.
- **`beFile p (some I)`** is now realized by the closed file's OsFs resources at a clean image,
  with the name durable or not; the revert state records a non-durable name.
- **`beFile_crash`'s claim is now true** (statement unchanged). Its `o' ∈ os` covers the vanish
  case.
- **`backend.Close`** can give `beFile p (some I)` for the file it created (`boltRelease` gives the
  resources at any `σ.named`).
- **Reopening it in the same generation** (a stop and restart after a first boot) uses a new 4c law,
  **`Bbolt.boltReopen_alloc`**: a durable image whose name may not be durable starts a database
  with `named := m.named`. This is true of bbolt's `Open`, and its crash case is OsFs's D4, as for
  `boltFresh_alloc`.
- `ReqReopen`'s durable-name Assumes is dropped.

**The consequence: a restart can panic, found while checking the fix.**
- If a crash takes the file's name away after the member's first *local* snapshot, the WAL keeps a
  snapshot record `k > 0`.
- The restart's `recoverSnapshot` then finds no backend (consistent index `0 < k`) and no
  `k.snap.db` (a local snapshot makes none), and panics (`bootstrap.go:482`).
- So no restartable `diskState` exists for such a disk, and `disk_crash` is not realizable there.
- Before the fix this was hidden: `beFile_crash` claimed, falsely, that the file survives.
- Filed as `nonissues/etcd-backend-name-lost-restart-panic.md` (`blocks-proof: yes`, pending a
  decision). `bbolt-create-dir-not-synced.md`'s claim that "etcd recovers from its WAL" now says
  this holds only before the first local snapshot.
- The gap is recorded in `disk_crash`'s docstring and `ApiBoot`'s header. See New decisions 3.

### G-b: renaming over an open backend. Fixed.

**New in 4a (`backend/Api.lean`):**
- `FileSt` (`closed o` | `opened γ L`);
- `beAt p d`, the destination's crash state: `beFile p o`, or `beDurInv γ p ∗ beHist γ L`;
- `beRenamedOver p os d`, what the rename leaves. A closed destination file joins the list
  (`o :: os`). An open one keeps its history and gets the new exclusive `beDetached γ p`, its entry
  pending;
- `beDetached_excl`;
- **`beCloseUpd`'s detached form.** For `d = some os`, the close of a renamed-over file gives no
  `beFile p`; its final image joins the list (`some I :: os`).

**New in `Durable.lean`:** `beDetached_crash`. At the crashed generation, the detached file's
history folds into the revert list as some `I ∈ L`. The new file's crash law then applies with the
extended list. Nothing is minted at `L'`, and the law consumes the history and the token.

**`Snap.dbFile_rename` and `OpenSnapshotBackend`'s update** take the destination as `beAt p d`.
- `applySnapshot` passes the open form: its old backend is open at the rename (`server.go:1068`)
  and closes later (`:1144`, `go oldbe.Close()`).
- `bootstrap`'s recovery passes the closed form: it closes the old backend first.

**A pre-existing mismatch, found and fixed while doing this.** `dbFile_rename` handed the renamed
`beFile` to the call's post. Since repair3-boot, `OpenSnapshotBackend`'s update puts it in the
client's state at the commit, so a crash between the rename and the return found it in neither. It
is now given at the commit.

**Remaining gap.** The detached entry's realization, like every revert entry, is the OsFs `rename`
gap: an inode that a rename unlinks while it is open. This is added to that entry in
`notes/perennial-changes.md`.

### Text updates, besides the above

- `NewServer.lean` round-2 paragraph;
- `New.lean`, `backend__Close.lean` and `OpenBackend.lean` Changes;
- `applySnapshot.lean` Changes: the recorded gap is now fixed in the callees;
- `snapshotHandler__ServeHTTP.lean` and `newSnapshotHandler.lean` Changes;
- the headers of `ApiBoot`, `Durable` and `backend/Api`.

## Replacement text for `top.md` K6

> **K6 — the history is the committed log's**: snapshots, restores, restarts and membership changes
> continue the same `σ`; an answered step is durable on a quorum. **Crashes** are Perennial's crash
> rule (the whole program's machine; every thread of the generation dies), at any point of a
> member's life. The program keeps each member's `EtcdServer.diskState` in its crash invariant, and
> its crash frame applies `EtcdServer.disk_crash`: 2e's one crash law per disk, from the old
> generation's `crashed` and OsFs's `crashRest`, over R1's `Raft.raftState_gen`/`raftState_crash`,
> the WAL's `walRecs_crash`/`walWriting_crash`, the snapshotter's laws and 4a's
> (`beFile_crash`, `beCrash`, `beDetached_crash` for a backend renamed over while open). It gives the
> next generation the disk, idle, at the kind the crash left. The cluster's resources serve every
> generation (`EtcdModel.etcdState_gen`, `etcdLb_gen`, `envUpd_gen`, `Raft.global`,
> `EtcdServer.srvNet_gen`, `srvEp_gen`, `Rafthttp.peerAddr_gen`). An address's protocols are a
> family set once for the run, each generation serving its own member (`Http.protoFam_gen`,
> `protoFam_at`), so a restarted member serves its peer address again and its client address with
> the next generation's contract. **The adequacy theorem's environment premises** for crashes,
> beside `ServerStorage.diskOk`: `Wal.crashInScope`, that every crash leaves each member's WAL so
> that `Open` + `ReadAll` returns records meeting `Wal.Recs.crashScopeOk` (at most one conf-change
> entry above the stored commit, `issues/raft-commit-lost-with-entries-kept.md`; no snapshot record
> above it; the user's decision, open question 2.8). The WAL's crash laws and `disk_crash` take it,
> so the proof has no out-of-scope case. **Pending the user**: a first boot's backend file, which
> `bolt.Open` creates with no directory sync, may vanish at a crash until `member/snap` is synced
> (its revert list holds `none`); after the member's first local snapshot the restart then panics
> (`nonissues/etcd-backend-name-lost-restart-panic.md`), so `disk_crash` is not realizable for that
> disk until a premise, a scope restriction or a fork fix is chosen. Recorded gaps (Perennial,
> `notes/perennial-changes.md`): how the crash frame takes `diskState` out of an invariant that the
> running server opens inside callees' atomic updates (a crash-aware invariant); and OsFs's `rename`
> (the realization of every revert entry: renames onto the backend's path, and a backend renamed
> over while open).

## Requests

### To the coordinator

- **`top.md` K6:** the replacement text above.
- **`open-questions.md` 2.8:** its verify-round line still names `crashOutOfScope γ ds`. Now the
  scope is W0's environment premise `Wal.crashInScope` (records meeting `Wal.Recs.crashScopeOk`),
  and `disk_crash` has no out-of-scope case. 2.7 likewise, if it names `crashOutOfScope`.
- **The open-question entry requested in `repair4-raft-crash.md`** ("4a `backend.Close` is not
  provable for a file created in the same generation") is resolved by G-a. Replace it with New
  decision 3.
- **New decisions 1-4 below** are for the user. 1 and 2 are trusted-boundary changes, and 3 is a
  scope decision.

## New decisions

1. **net/http's protocols are per generation** (F3). This changes the HTTP boundary the user
   reviewed (2026-10-22, decision 1: "an address string's protocol is fixed once").
   - What is fixed once is now a family of protocols, one per generation (`protoFam`), and
     `protoAt` is the current generation's.
   - It is true of Go: a crash kills every connection, and no request crosses it.
   - It is needed because etcd's client contract names per-generation lease views, which a crash
     loses. With one protocol for the run, a member restarted after a crash could neither serve the
     first generation's contract nor reserve its own. The alternative was to index W0's lease views
     by an incarnation, which changes the client API.
   - It withdraws repair3-boot's `protoAt_gen` and 2f's `raftProto_gen`, and changes the posts of
     `cluster_alloc`, `urls_reserve` and `srvEp_reserve`.
2. **A new trusted net/http law, `addrFree_protoAt_excl`, and `srvEp_agree` within one cluster**
   (F5).
   - The law is true of the set-once map.
   - `srvEp_reserve` becomes a fancy update at the new namespace `srvEpN` that takes `srvNet`. It
     opens the cluster's own address map, which `cluster_alloc` allocates.
   - Cross-cluster agreement (`γ = γ'`) is dropped: it is not realizable from net/http's API, and no
     user needs it.
3. **A first boot's backend file may vanish at a crash, and the restart then panics** (G-a).
   - What the code does: `bolt.Open` creates `member/snap/db`, and nothing syncs `member/snap`
     unless the member receives a snapshot from the leader.
   - When it goes wrong: on a file system that drops unsynced names at a power loss (POSIX as
     written, OsFs's model), a crash after the member's first local snapshot loses the backend. The
     member's restart then panics with "failed to recover v3 backend from snapshot" and does not
     come back until an operator acts. ext4 (`data=ordered`) and xfs keep the name with the file's
     first sync, so etcd does not see this in practice.
   - The specs now say the file may vanish, which is true. `disk_crash` cannot be realized for that
     disk until one of these is chosen:
     - **(a)** an environment premise "a created file's name is durable at its first sync" (the
       ext4/xfs fact). OsFs would need that crash-rule variant (Perennial), and bbolt's
       `BoltSt.named` would become true at `Open`'s initial sync, which revisits A11 F1's decision.
     - **(b)** a scope restriction: no crash before `member/snap` is synced. That excludes almost
       every crash of a member that never received a snapshot.
     - **(c)** a fork fix: `fileutil.Fsync(cfg.SnapDir())` after `OpenBackend` creates the file.
   - (c) is the smallest and matches what the WAL does. (a) states what etcd relies on in practice.
4. **G-b's detached file** (`beDetached`, `beCloseUpd`'s detached form, `beDetached_crash`). This is
   new client-visible vocabulary in 4a's file API, for `applySnapshot`'s rename over the open old
   backend. Its realization is the OsFs `rename` gap, the same as every revert entry.

## Build

- The changed vocabulary modules (`wal/Api`, `net/http/Api`, `bbolt/Api`, `backend/Api`, `Durable`,
  `snap/Api`, `grpc/Api`, `rafthttp/Api`, `ApiBoot`): **OK (9 modules)**.
- Every `Spec` importer of every changed file (`etc/importers.py --leaves --git HEAD`, the `Spec`
  leaves; rerun after the last docstring edits to `ApiBoot`): **OK (1231 modules)**,
  `Build completed successfully (3741 jobs)`, no errors.
- Snippets: `go vet ./specreq/{etcdserverboot,v3rpc,backend,rafthttp}/` clean, `gofmt -l specreq/`
  empty. `etc/issues-status.py --check` passes, and the indexes are regenerated.
