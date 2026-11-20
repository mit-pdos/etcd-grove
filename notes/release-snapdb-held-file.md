---
title: storage.storage.Release.wp_proof is false (ReleaseSnapDBs deletes a snapshot file a caller holds)
found: 2026-11-17
by: etcd-grove-03's releasesnap attack (/shared/tmp/releasesnap-attack/); Go test examples/axiomcx/releasesnap
blocks-proof: no (no current proof is known to reach it: etcd Releases after the rename, the fork's fix for issues/etcd-release-snapdb-before-open.md)
status: route closed on branch wal-link (T1, 2026-11-17); the axiom itself goes at the WAL link's L3
---
# `storage.storage.Release.wp_proof` is false

A bug in this repository's trust base. The axiom
(`Proof/go_etcd_io/etcd/server/v3/storage/storage__Release.lean:26`) frames every resource the caller
holds, but Go's `Snapshotter.ReleaseSnapDBs` deletes every `<hex>.snap.db` below the index by
listing the directory, including a file a caller already took out of `snapDirInv`'s map `M` with
`SnapRO.snapDir_take` and still holds as `backend.fileHolds`. `snapDir_take` with `Rm = snapRmM`
hands exactly the `□ (∀ j < i+1, Rm j)` a `Release` at `i+1` needs. So a proof can take file `k`,
release at `k+1`, open the file and conclude it holds `D`; in Go the file is gone.
`examples/axiomcx/releasesnap/releasesnap_test.go` (`TestAttackHeldFile`: panics with "claim: the
held snapshot file holds D"; the test passes).

**Reach.** 25 collections list the axiom. No current proof is known to take a file and then release
below it: etcd releases after the rename (the fork's fix for
`issues/etcd-release-snapdb-before-open.md`). But the axiom would verify that bug if it came back.

**Fix.** In the WAL link's L2: seal `snapDirInv`, drop `snapDir_take` as a client lemma, and have
`OpenSnapshotBackend` take the file at its rename.

**Status (2026-11-17, branch `wal-link`).** The route is closed by T1: `snapDirInv` is sealed
(`rafthttp/Net.lean`), the take is a generic sealed token `snapHeld p D R'` (`storage/SnapHeld.lean`,
`@[no_expose]`, gated in `etc/import-all.txt`) consumed only by `OpenSnapshotBackend` at the rename,
`snapDir_take` is no longer a client lemma, and the narrower axiom `snap.Snapshotter.ReleaseSnapDBs.wp_proof`
(attacked twice: round 1 refuted, round 2 survives, `notes/axiom-review/releasesnapdbs.md`) frames no
held file. `storage.storage.Release.wp_proof` itself stays an axiom until L3, where `storage.Release.spec`
is replaced in place by the proved statement (`ReleaseNext.lean`, from `ReleaseLockTo` + `ReleaseSnapDBs`)
and the axiom is removed.
