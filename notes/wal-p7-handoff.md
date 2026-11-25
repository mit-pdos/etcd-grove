# P7 handoff (D6-T6, the snapshot directory's crash law) — START HERE

Branch `etcd-safe-p7`, worktree `/shared/etcd-grove-p7` (#50 P7, sub-issue #53). Base `211ef407a2`
(`etcd-safe-d6t6impl/2026-11-24`), lean `6c5b77f34a` merged (dist statements and `NewServer.specC` moved to
lean's `HEnv : EtcdVerifyOff`).

State (2026-11-25, head `5b2eefe356` and after): **`snapDir_crash.law` is proved** (`snapDir_crash_law_holds`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/SnapDirCrash.lean`, a defs module, no `sorry`, no axiom; checked with
`etc/lean-check.py -a`). The coordinator's round-4 decisions (`notes/etcd-dist-d6.md` §T6 round 4) are implemented:

- `rafthttp/Net.lean`: the handle `snapDirInvH sd γd img Rm` (`∃ γk, inv snapDirN (snapDirInvK …)`), the body
  `snapDirBody` (`@[no_expose]`: files `M` durable (`fileAtDur`, index in the saved `E`) or pending (`fileAtPend`),
  exact free names `F` (`fileFreeDur`), `snapSaved` for `E`, `Rm` for `E` minus `M`), the crash side
  `crashed ∗ token γk`, `snapDirKeep` (the handle with its token; `snapDirKeep_handle`), `snapDir_init`, and
  `snapDir_take` now an `|NC={⊤}=>` update. Every user renamed to `snapDirInvH`.
- `backend/FileDur.lean`: the durable file predicates (`fileAtDur`, `fileAtPend`, `fileFreeDur`, `nameCrash`,
  `fileHoldsMDur`) and their crash lemmas; `bbolt.boltImageRcpt_gen` (proved API law).
- `TouchDirAll.spec`'s post: the new directory's names other than `.touch` are committed (ledger 2026-11-25);
  `BootSnapCarve.lean`/`bootstrapSnapshot.lean`: the carve gives durable free names.
- Docstrings of `SaveDBFrom`/`ReleaseSnapDBs`/`storage.Release`: link → pending in `M`, dir sync → `E`, a removed
  pending index joins `E` with its `Rm` (statements unchanged but for the handle);
  `nonissues/etcd-snapdb-removed-before-dirsync.md` (reachable, harmless).
- The law (`snapDir_crash.law`): old `snapDirKeep`, `crashed`, `£ 1`, `□ (∀ j, Rm j -∗ Rm' j)`, T7's
  `snapDirKept` and pure `lookupH R V' sd = some (.dir J)`, `osSharedInv ∗ crashRest … D …` (taken files `D`
  not named at `J`'s snapshot names), the new generation's `snap.snapDirOwn` and `snapSlot` on every index ⇒
  new `snapDirKeep … Rm'` and `crashRest … (D' ++ D)`. Generations at the statement's Go context (`atC`).

Left for T7 (the consumer): thread `snapDirKeep` out of `NewServer` (it now drops the Keep after
`snapDirKeep_handle`, NewServer.lean ~1228); prove `snapDirKept`/`lookupH` from `TouchDirAll`'s parent syncs;
produce `snapSlot`s and `snapDirOwn` at the new generation (a carve from the restarted `member/snap` claim);
supply the `D` premise. Build evidence (head `01212f3ee0`, fk-lean2 worktree `wt/etcd-safe-p7`, log
`/home/ubuntu/eg/logs/etcd-safe-p7-20261125-054350.log`'s successor, local copy `/shared/tmp/p7/remote2.log`):
the change's 163 leaves; every P7 module built; 6 failures not P7's: dist D2's `deployment`/`kvremote`
`InitLinked` and `server`/`client` `PkgTable` (the base's gen-init diffs against lean's newer commits:
`ContextReadErrs` gone, `log.NewModel`) and `mvccfull`/`mvccrand` `TopLevelWitness` (`simp` no progress at
line 41, base × lean).

Next (coordinator, 2026-11-25): stack on `etcd-safe-main-pin/2026-11-24` @ `3717c7903b`. A trial merge
(`git merge-tree`) gives 50 conflicts (client `levelTok 0`, kvnet→kvraft deletions, `EtcdVerifyOff` in the dist
statements, RaftTla tracecheck, etc/goose.py, notes): reported before resolving, as asked.


Pin: the etcd re-pin `e94f33b50` does not change `server/etcdserver/api/snap/` (only `storage/backend.go`'s
OpenSnapshotBackend directory sync, owned by `etcd-safe-main-pin`), so this branch stays on lean's pin.

After the merge, `etc/gen-init.py --check` reports 15 differences that lean itself does not have (lean: clean):
the base's D2 config adds a main-tree `examples/lib/remote` Init, which makes the Dsverify and `Net/` remote
initializers import it and declares `Net/`'s stale. Left as committed (not regenerated) for the lead: the two
trees' remote initializers declare the same names, so the generated result needs a decision.
