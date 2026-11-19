---
title: snap.snapDBPath, an opaque function of the snapshotter's location, made the multi-member boot premise unsatisfiable
found: 2026-11-19
by: the B1 attack (wal-link, fresh read-only agent, axiom skill), /shared/tmp/wallink/attack-b1.md section 3
blocks-proof: no
status: the collision fixed on wal-link (2026-11-19, approved by the user via etcd-grove-03); satisfiability of the boot premise still blocked by notes/datadir-relative-unsat.md (pre-existing, found by the re-attack)
---
# The snapshot paths were a pure function of a run's location

A bug in this repository's trust base (the bootstrap contract, a premise of the closed theorems), not
in etcd.

**What was stated.** `snap.snapDBPath : Loc → w64 → GoString` was opaque: the path of the database
snapshot of index `i` of the snapshotter at location `ss`. `bootOk`'s and `bootOkR`'s `Hssp` (the
bootstrap contracts' posts, `InvBoot.lean`, `InvRestart.lean`) said
`snapDBPath bs.ss' = snapDBPathOf cfg.DataDir`, `bs.ss'` the snapshotter `bootstrap` allocates in this
run; the specs of `DBFilePath`, `SaveDBFrom`, `ReleaseSnapDBs`, the directory invariant `snapDirInv ss`
and `OpenSnapshotBackend` were over `snapDBPath ss`.

**Why it was wrong.** An opaque Lean function has one interpretation for every execution, but the
location of a member's snapshotter is chosen by the allocator per run: any location `l` is member 1's
snapshotter in some run and member 2's in another. For the contract (a claim about Go, the premise of
the closed theorems) to be true in every run, `snapDBPathOf d1 = snapDBPath l = snapDBPathOf d2` for
the data directories `d1 ≠ d2` of two members. Then, in one run, the members' contracts hand out
exclusive claims on the same names: since S5 (2026-11-18) `Hsfree`, the shared-mode claims
`snapFreeAll (snapDBPathOf dd)` on every index's snapshot name (`osNames j (.only [b]) (own 1)`), and
since B1 (2026-11-19, unlanded) also `Hpath`, the backend's `bPath` on `backendPathOf dd`
(`snapDirOf d1 = snapDirOf d2` follows once `snapDBPathOf` is a definition). No resources satisfy
three such posts at once, so the contract is false of Go (Go's `bootstrap` does return for each
member), and **every closed theorem whose program boots two or more members held vacuously since S5**:
putget3/putgetN, auth3/authN, leaseN, leaseexpiryN, leasecatchup, restart (three members), restartN,
partition, txnlin/txnlinfaultsN where they start a cluster, the k8s compactor and etcd3 (cluster3),
and their `_robust` forms. The one-member theorems were not affected (one data directory). Not
derivable as `False` inside Lean: the contract's location is existential, and no entailment from bare
points-to cells concludes the equation, so it is a premise-truth (vacuity) defect of the
cross-world kind (`.claude/skills/axiom/SKILL.md`, "A cross-world entailment"; as
`notes/incomingof-crossworld.md`).

**Fix (wal-link, 2026-11-19, approved by the user via etcd-grove-03).** The snapshotter's directory is
its `dir` field (Go: `snap.Snapshotter{lg, dir, fsyncDir}`, `dir` written only by `snap.New`), a
persistent cell inside `isSnapshotter ss sd` (`snapDirAddr ss ↦□ sd`, as `snapLgAddr` for the logger),
with `⌜∃ dd, sd = config.snapDirOf dd⌝` (the only snapshotter etcd makes is
`snap.New(cfg.Logger, cfg.SnapDir())`). The heap fixes the directory per execution. Paths are a
definition over the string, `snapDBPath sd i := sd ++ "/" ++ snapDBName i`; `snapDBPathOf dd` is gone
for `snapDBPath (config.snapDirOf dd)`; `snapDirInv` is over `sd`; `DBFilePath`, `SaveDBFrom`,
`ReleaseSnapDBs`, `storage.Release` (and `isWalStorage`'s `Release` law), `OpenSnapshotBackend`,
`applySnapshot`, the transport's and the handler's specs take `isSnapshotter ss sd` and `snapDirInv sd`;
`bootOk`/`bootOkR` give `isSnapshotter bs.ss' (config.snapDirOf cfg.DataDir)` in place of `Hss` and
`Hssp`; `srvDiskImageAt` holds the invariant of `config.snapDirOf dd` (no stopped snapshotter's
location). `snapDirInv_ss_congr` is gone (no longer needed). The independent re-attack, including a
satisfying assignment of the boot premise for k members (over absolute data directories), is in
`notes/axiom-review/snapdir.md`. It also found that the examples' data directories are relative while the
file claims need absolute paths, which keeps the boot premise unsatisfiable for every member on another account
(pre-existing since S5): `notes/datadir-relative-unsat.md`, open.
