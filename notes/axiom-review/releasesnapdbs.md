# `snap.Snapshotter.ReleaseSnapDBs` (axiom review, 2026-11-17)

**Reviewed** (wal-link L2, the proposal of 2026-11-17, an independent attack for etcd-grove-03): the
proposed trust-boundary spec of `ss.ReleaseSnapDBs(snap)` (the `snapDirInv` half of today's
`storage.storage.Release.spec`): the snapshot directory's invariant `inv snapDirN (snapDirInv ss γd
img Rm)` with `□ (∀ j < i, Rm j)` for `i = snap.Metadata.GetIndex()`, post `err = nil ∨ ¬ releaseOk`;
with `snapDirInv` and `snapDir_take` (`Proof/.../etcdserver/SnapRO.lean`), `SaveDBFrom`,
`OpenSnapshotBackend`, `os.Rename`, and the existing axiom `storage.storage.Release.wp_proof`
(`Proof/go_etcd_io/etcd/server/v3/storage/storage__Release.lean`), which says the same of the
directory.

Go at the etcd pin `8c28a4296` (`server/etcdserver/api/snap/snapshotter.go:45-72`, `db.go`).

## Verdict

**Refuted** (Go side; the Lean side is the frame rule). Go removes every `<hex>.snap.db` entry below
`i` that it finds by *listing the directory*, not only the files the invariant holds in `M`. A caller
that took file `k` out of `M` by `snapDir_take` (a client lemma: it hands out
`backend.fileHolds (snapDBPath ss k) D` and, with `Rm = snapRmM γm`, raises the removal counter to
`k + 1`, which is exactly the `□ Rm k` a `ReleaseSnapDBs(k + 1)` asks) keeps `fileHolds` across the
call by the frame rule, while Go deletes the file; `OpenSnapshotBackend`'s rename then fails
(`ENOENT`), or a `bolt.Open` of the path creates an empty database, not `D`. The same flaw is in the
existing `storage.storage.Release.wp_proof` (same premise, same frame).

Go checks: `examples/axiomcx/releasesnapdbs/releasesnapdbs_test.go` (copied from the attack's
`releaseattack_test.go`, in package `snap` there; external package here, assertions instead of the
attack's panic), both pass at the pin:

- `TestAttackHeldFile`: `SaveDBFrom(img, 5)`, `DBFilePath(5)` (the held path), `ReleaseSnapDBs(6)`:
  the held file is gone; `bolt.Open` of it gives an empty database.
- `TestAttackNames`: what `ReleaseSnapDBs(10)` removes, below.

## What Go removes, and when it errs (`TestAttackNames`)

Each directory entry whose name ends in `.snap.db` (case-sensitive) and whose prefix parses by
`strconv.ParseUint(prefix, 16, 64)` to a `j < i`: canonical names (`0000000000000005.snap.db`) and
non-canonical ones (`5.snap.db`, `0000000000000000005.snap.db`, `9.snap.db`), and an **empty
directory** of such a name (`os.Remove`). Kept: `j ≥ i` (also uppercase `000000000000000A.snap.db`,
10), unparsable prefixes (`0x5`, `5_0`, `+5`, empty, 17 digits), the suffix in another case, a
non-empty directory (its `Remove` fails: logged, skipped), and every other name (`tmp*`, `*.snap`,
the backend's `db`). Errors: only from `os.Open(s.dir)` and `Readdirnames` (a missing directory);
a failed removal is logged and **not** returned (so the proposal's `releaseOk` read "a failed close
or removal" wrongly). A nil `Metadata` reads index 0 and removes nothing.

## Decision (etcd-grove-03, 2026-11-17): Fix (A)

Seal `snapDirInv` (`@[no_expose]`; keep `snapDir_init`, `snapDirInv_ss_congr`), drop `snapDir_take` as a
client lemma, `OpenSnapshotBackend.spec` (proved) takes the file at its rename; `ReleaseSnapDBs.spec`
as proposed plus (m2) post `err = nil ∨ ¬ snap.dirReadOk ss`, (m3) `isSnapshotter ss` in the premise,
(m4) a docstring saying what Go removes and why that is sound. The corrected text gets a second
short attack before the axiom file is added.

## The corrected text (survived the second attack; in the tree as `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Snapshotter__ReleaseSnapDBs.lean`, the docstring updated for T1)

`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Snapshotter__ReleaseSnapDBs.lean` (imports as
`Snapshotter__SaveDBFrom.lean`, plus `Proof.go_etcd_io.raft.v3.InvPb` for `smOpt`):

```lean
/-- **`ss.ReleaseSnapDBs(sn)`** (`server/etcdserver/api/snap/snapshotter.go:45-72` at the etcd pin;
names only; wal-link L2, 2026-11-17): `sn`'s metadata read at index `i = md.Index` (a nil
`Metadata` reads `0`), the snapshot directory's invariant at any removal fact `Rm`, with `Rm j` for
every `j < i`: `nil`, or an error when the directory cannot be listed (`¬ dirReadOk ss`).

What Go does: it opens and lists `ss`'s directory (the only errors), and removes each entry whose
name ends in `.snap.db` and whose prefix parses as a base-16 `uint64` below `i`
(`strconv.ParseUint(prefix, 16, 64)`); a failed removal is logged and skipped
(`examples/axiomcx/releasesnapdbs`, `TestAttackNames`). Why the statement is true of it:
* A canonical name is `snapDBPath ss j`. Such a file is either in the invariant's `M`, or held by a
  caller of the take lemma (`snapDir_take`, sealed: it hands out no `fileHolds`, only a token that
  `OpenSnapshotBackend` consumes at its rename), whose premise refutes `Rm j` and which keeps the
  resource that could produce it sealed until the rename: so no caller of this function holds
  `Rm j` for a held `j`, and Go removes only files in `M` below `i`. At each removal the file leaves
  `M` with its removal fact `Rm j` (given); a file whose removal failed leaves `M` too (forgetting
  its `fileHolds` is sound; a later `SaveDBFrom` of `j` keeps the file, `j` saved already). A file
  linked by a concurrent `SaveDBFrom` after the listing is not removed and joins `M`.
* A non-canonical name (`5.snap.db`, 19 digits, uppercase hex) and an empty directory of such a
  name: no spec gives `fileHolds` or `pathOwn` of such a path (`snapDBPath` is canonical, the
  backend's file `config.backendPathOf` is `<dd>/member/snap/db`, temporary files are `tmp*`), and the
  environment clause of `snapDirOwn` says nothing outside the server's snapshotters writes
  `.snap.db` files there (`SaveDBFrom` writes only canonical names). Removing one changes nothing
  the logic states.
* Nothing else is touched: `tmp*` files (a concurrent `SaveDBFrom`'s), `*.snap`, the backend's `db`
  (`OpenSnapshotBackend`'s rename target) do not end in `.snap.db`.
The post does not say that the files below `i` are gone (a removal may fail silently): the caller
gets nothing but the invariant kept. -/
abbrev snap.Snapshotter.ReleaseSnapDBs.spec : Prop :=
  ∀ (ss sn mp : Loc) (dq dq' : DFrac) (md : SnapshotMetadataM) (γd : GName)
    (img : w64 → backend.Data → IProp GF) (Rm : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗
      isSnapshotter ss ∗
      sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
      inv snapDirN (snapDirInv ss γd img Rm) ∗
      □ (∀ j : w64, ⌜uint.Z j < uint.Z md.Index'⌝ -∗ Rm j) }}
    (App (Val (ss @!! go.GoType.PointerType
        _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter.ty @!!
        go!"ReleaseSnapDBs")) (Val #sn))
  {{ (err : GoInterface), RET #err;
      sn.[raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
      ⌜err = GoInterface.nil ∨ ¬ dirReadOk ss⌝ }}
```

## Open: the take's form (for etcd-grove-03)

Fix (A) as worded moves the take into `OpenSnapshotBackend` (`∃ D` returned at the rename). The
server needs `D` before that call: `applyAll` (`ApplyAllSnap.lean:499-516`, `:1022-1035`) takes the
file, then derives the image's facts from `□ img i D` (`snapRecv_imageR`/`snapRecv_imageOnR`: the log
`A'`, `u`) and makes the KV's ghost jump, and `applySnapshot.specSnapM` is stated over that `D`
(`fileHolds … D`, `mvccImage D …`, `hA'`, `hlease`, `hauthI`, …). Nothing ties a `D` read before the
call to the one the rename finds, without a second ghost map in `snapDirInv`. Two forms:

- **(T1) the take stays, sealed** (recommended): `snapDir_take` moves into `rafthttp/Net.lean`, generic:
  `£ 1 ∗ inv snapDirN (snapDirInv ss γd img Rm) ∗ snapSaved γd i ∗ R ∗ □ (R ∗ Rm i -∗ False) ∗
  (R ==∗ R' ∗ □ Rm i) ={⊤}=∗ ∃ D, snapHeld (snapDBPath ss i) D R' ∗ □ img i D`, where `snapHeld p D R'`
  (`@[no_expose]`, `fileHolds p D ∗ R'`, in a storage module that `OpenSnapshotBackend`'s proof alone
  imports with `import all`) replaces `fileHolds` in `OpenSnapshotBackend.spec` (success: `R'` back
  with the backend; error: `snapHeld` back) and in `applySnapshot`'s premise (with `R' :=
  monoNatAuthOwn γt 1 nt`, dropping that premise: `SnapApplyWalk` uses the counter only after the open,
  `:728`). The removal fact is produced by a basic update (no invariant opened), so no other thread
  can hold `Rm i` while the token exists, and `R'`, the only thing that could make more, is sealed in
  it. `D` is fixed at the take, as today. No change to `SaveDBFrom`'s text.
- **(T2) the take in `OpenSnapshotBackend`, as worded**: `applySnapshot.specSnapM` restated over `∃ D`
  found at the open, the image facts and the KV jump moved from `applyAll` into `applySnapshot`'s
  proof (`SnapApplyWalk.lean`, 1108 lines; both `applyAll` arms); est. 500-1500 lines, and the
  window between the take and `os.Rename` (a plain triple, not atomic) still needs T1's update
  argument.

Either way the `ReleaseSnapDBs` text above is unchanged (it names only `snapDirInv`); its soundness
argument's first bullet is T1's. With T1 or T2 the existing `storage.storage.Release.wp_proof` is no
longer refuted by this attack (same argument); L2 replaces it by a proof from `ReleaseLockTo` and
this axiom.

**Decided (etcd-grove-03, 2026-11-17): T1.** Implemented: `storage.snapHeld` (`Proof/go_etcd_io/etcd/server/v3/
storage/SnapHeld.lean`, `@[no_expose]`, intro law only), the generic `snapDir_take` and
`snapDirInv_ss_congr` in `rafthttp/Net.lean` (`snapDirInv` `@[no_expose]`), `SnapRO.snapRmM_take` (the
server's refutation and update at `snapRmM`), `OpenSnapshotBackend.spec` over `snapHeld … R'` (`R'` back
on success, the token back on an error), `applySnapshot` taking `snapHeld … (monoNatAuthOwn γt 1 nt)`.

## Round 2 (2026-11-17, an independent attack for etcd-grove-03)

**Verdict: the corrected text survives, and T1 closes the round-1 counterexample**, on one condition
(major), applied: the seal is gated, `etc/import-all.txt` lists `sealed …storage.SnapHeld` with
`allow …SnapHeld …OpenSnapshotBackend` (and `rafthttp.Net` was sealed there already), with a comment
that `ReleaseSnapDBs`' (and `storage.Release`'s) soundness depends on it, as the WAL axioms' on
`WalRecs`. Minors, applied: the take's refutation premise is a plain wand `R -∗ Rm i -∗ False`
(sound: it is used only in the branch where the file is absent, where it consumes `R` to refute the
invariant's `Rm i`; the other branch drops it and uses the update on the same `R`), now said in its
docstring; the docstring says the argument holds for a removal fact that only ghost updates make (a
`Rm` a physical step or a pure fact could make true would escape "no other thread's resources
change"; the server's `snapRmM` is a counter's lower bound). Optional `snapHeld_forget : snapHeld p D R'
⊢ R'`: not added (no path abandons the token: `applySnapshot`'s error arm of `OpenSnapshotBackend` is
refuted by the environment premises).
