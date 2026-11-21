# wal-nostorageok handoff

## START HERE (2026-11-21) — HARD STOP at step 1: the two `os` field classes cannot be proved

- Worktree `/shared/etcd-grove-walns`, branch `wal-nostorageok` off `pin-04b` (`9ac46cf77e`, Perennial
  `04b42a139`; `--packages=/shared/tmp/manifest-04b.json`, `PERENNIAL_DIR=/shared/perennial-04b42a139`).
  Nothing built, no source edited; `.lake/build` not seeded.
- Goal: `rnNewStorageOk` out of the closed statements. `rnNewStorageOk_law_holds` (`RnNewStorageLinked.lean`)
  needs only `[os.fileStat.FieldAssumptions] [os.file.FieldAssumptions]` beyond the server's `Assumptions`.
- **Finding (step 1).** The two classes (`TrustedCode/os.lean`) are hypotheses on the semantics, not facts
  about the translated code: each field is `go.IsGoStepPureDetTagged under (StructFieldGet/StructFieldSet
  file.underlying f) ...`. Perennial `04b42a139` has no generic step for `StructFieldGet (go.StructType fds)`
  (`Golang/Defn/PostLang.lean` only reduces a named type to its underlying one); every translated struct gets
  these steps as fields of its generated `T.TypeAssumptions` (hence of its package's `Assumptions`, which the
  closed statements bind). goose emits none for `os.file`/`os.fileStat` because their layouts are trusted
  (`file.TypeAssumptions` in `Code/os.lean` has only `type_repr`, `underlying` and the method sets). So no
  proof from the translated `os`, under any pin, without one of:
  - **(A) the closed statements bind them** — `[os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]` as
    instance binders (as `mvccfull`, `mvccrand`, `bboltfs`, `walfs`, `crashlog` already do), in place of the
    premise `rnNewStorageOk`. No trusted text changes (the classes are trusted text already, in the tcb).
  - **(B) goose emits them**: a Goose configuration entry giving a trusted type's layout, from which goose
    writes the get/set steps into `T.TypeAssumptions` (so `os.Assumptions`, already bound through every
    package's `Assumptions`); `TrustedCode/os.lean` drops the two classes and every closed statement binding
    them loses the binders. A Perennial (goose) change through its own workflow, plus a trusted-text change.
- Recommendation: (A) now (the step-2/3 plan unchanged otherwise), (B) recorded in `notes/perennial-changes.md`
  as the general follow-up.
- Closed statements that change under (A) (the ones whose premises reach `rnNewStorageOk` through
  `etcdstart`'s `commonPremises`/`OneMember.premises`/auth/leaseexpiry/putget3 `Defs`): `etcd_robust.spec` and
  `etcd_safe` (`examples/etcd/all`), `etcd_leaseexpiryN_robust.spec` and its closed theorem
  (`examples/etcd/leaseexpiryN`), `k8s_robust.spec` and `k8s_safe` (`examples/k8s/all`); to be confirmed by
  the tcb report after the build (`k8s_authz` does not start etcd).
- Next (after the decision): seed `.lake/build`, then the 72ce32ea4e template (link list
  `=rnNewStorageOk_law_holds raftpb.SnapshotMetadata.wp_GetIndex` or a server-Link wrapper; the law as
  `newRaftNode.wp_proof`'s hypothesis; `#Hns` out of the specs/premises/Mains' `icases`), threading the two
  instances up to the closed statements (A); build; stop before the closed statements' edit is final.
