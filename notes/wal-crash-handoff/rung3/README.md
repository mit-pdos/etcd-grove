# Crash rung 3 (bbolt/mvcc under crashes): handoff, 2026-11-12

**Status: handed off, not continued here.** The user decided (2026-11-12) that a collaborator picks up
the WAL work and unifies the crash models (this repository's abstract-disk extension `absDiskExt`,
used by the WAL spec, and the per-byte Linux model in `LinuxFs/`), so rung 3 is not continued by the
etcd-grove-81 sessions. This directory keeps what rung 3 found, because its working material lived in
`/shared/tmp`, which is not durable.

Files here:
- `README.md` (this file): where things are, what is done, what is open.
- `scope.md`: rung 3's Scope, with every decision (the user's and etcd-grove-81's) at the end.
- `freeze-r3-3.md`: the Freeze package of the trusted bbolt crash spec (R3-3/R3-4), as submitted for review.
- `review.md`: the independent Freeze review's findings, three lenses (axiom, spec, LinuxFs comparison),
  with the verifiers' verdicts.

## Where the work is

- **Branch `crash-rung3`**, worktree `/shared/etcd-grove-rung3`, **not landed** on `lean` (10 commits
  on top of lean `b4f0711091`, e8cebf8300..7632f56ede). Its own handoff: `notes/wal-crash-handoff/rung3-handoff.md` on
  that branch; decisions in the worktree's untracked `questions.md`. It does not touch
  `GooseLang/Ext/Durable` (W4c's fresh-ghost-names crash change landed on lean, 5961b2f46a; a merge
  would build on it).
- **bbolt fork**: `upamanyus/bbolt`, branch `goose-lean-v2`, local checkout `/shared/tmp/bbolt-fix/bbolt`.
  Commit **`4f08974e` (D7) is local, not pushed**; the branch `crash-rung3` pins it (etc/goose.py project
  `bbolt`, `examples/go.mod`). The fixes before it (`c5a6065` Open syncs before its first commit,
  `ea4cab5` Open closes on a failed sync) are on lean and pushed.

## What is done (on the branch)

- **R3-0, the tester and driver**: `examples/etcd/mvcccrash` (goose-translatable; `Boot` after every
  crash opens backend, cindex hooks, lessor and mvcc as bootstrap/NewServer wire them, oracle in
  `lib/durable`), the crash driver `crash_test.go` + `crashtest/crashsim` (ptrace-recorded incarnations;
  posix/ordered images with and without garbage on unsynced sectors, kill, kill-then-power; targeted
  modes `-target`, `-killdb`, `-window`, `-first`).
  - Option (b): the tester's db spans several pages (100 keys, values 64-511 B).
  - The tester loads the consistent index right after `SetBackend`, as etcd's `bootstrapBackend` does
    (`bootstrap.go:273`); before that, a no-op `ForceCommit` synced before any write and hid the bug.
- **D7**: bbolt `Open` re-runs init when `initTorn` holds (fork `4f08974e`); `Open.wp_proof` re-proved over
  a new proved `DB.initTorn.spec_own` and `Meta.Magic.spec`; interfaces regenerated. **Incomplete**: see
  B2 below.
- **Controls** (40 chains x 6 incarnations x 30 images, seed 11, kill 0.8):

  | bbolt | mode | images | violations |
  |---|---|---|---|
  | unfixed `743299d8` | `-killdb -window`, target 0.8 | 7,110 | 127 (116 kill-then-power corruption, 8 torn init, 3 other) |
  | D7 `4f08974e` | same | 7,200 | 0 |
  | unfixed | standard, target 0.6 | 7,020 | 16 (11 corruption, 4 torn init, 1 hang) |
  | D7 | standard | 7,200 | 0 |

  This confirms `issues/bbolt-open-unsynced-meta-kill-then-power-loss.md`'s impact on etcd's boot order.
  The crash recorder occasionally hangs under ptrace (3 incarnations; a per-incarnation timeout in
  `RecordKill` is a to-do).
- **Findings recorded**: `nonissues/bbolt-fork-init-garbage-meta.md` (on the branch; a case of bbolt#567).

## What is open (from the Freeze review, `review.md`)

Verdict NOT READY. The blockers and majors, all verified:

1. **The tracked-file axioms do not require durable's reservation** (axiom lens B1): durable in its
   unreserved mode may write the hidden tracked path, and `Open_kv_trk` then reads a ghost ∅ while Go reads
   the image. The same bug class as WAL W4a's round-2 B-1. Fix: `durableResvD r` in `Open_kv_trk`'s pre.
2. **D7 is incomplete** (axiom lens B2; LinuxFs lens B1): `initTorn` tests the magic number and init's page
   headers, not "no meta validates". Six images a power loss can leave under the approved assumptions (and
   per-byte old/new mixes) still fail `Open` at `4f08974e`. Fix (fork): re-run init when the file is at
   most 4 pages and neither meta validates (checksum included); minibolt's proved rule is the same.
3. **Gate G1 is not enforced** (axiom M1, spec M1): option (U)'s `dbUntracked` witness is sound only if no
   `fileHolds` names a tracked path; `goose_adequacy_start_files` is generic over the extensions, so a
   crash-free program can mint both.
4. **Open's commit point** (axiom M2, spec/LinuxFs m1): `BoltOpen` must commit only on a successful
   fdatasync.
5. **Evidence gap** (LinuxFs M1): crashsim keeps whole 512-byte sectors (old, new, torn prefix, garbage);
   it never produces per-byte old/new mixes, the realistic images on Linux/ext4 that defeat structural
   checks like the magic number. Add a `bytemix` mode and rerun the controls.
6. Spec lens: D3 (`noSync`/`noGrowSync` in the backend's options) needs trusted text the package does not
   write out; the minors listed in `review.md`.

## For unifying the crash models (the LinuxFs lens's comparison)

- **Agreement**: the bbolt arm's claims agree with the per-byte model except the torn-init point (2 above).
- **World assumptions**: the arm's are weaker than LinuxFs's on byte values (arbitrary unsynced bytes vs
  each byte old or new) and on directories (bare `fsync(2)`, no journal order, vs ext4's configuration C).
- **Restarts (important)**: LinuxFs assumes every restart follows a machine reboot or a supervisor
  `sync(2)` (`GooseLang/Ext/Fs/Impl.lean`, "Restarts"; `notes/fs-semantics-v2.md`). The arm models a
  process kill without sync and kill-then-power-loss, which is exactly where the bbolt bug fixed by
  `c5a6065` lives. A proof over today's per-byte model would assume that bug away; replacing the trusted
  arm needs a process-kill crash in `fsExt` first.
- **Estimated path to replace the arm by a proof**: process kills in `fsExt` (1-2 wk), finish the real-bbolt
  port (`notes/bbolt-port-plan.md`, 2-3 wk), a crash invariant for real bbolt modelled on minibolt (6-10 wk),
  a refinement or move of the tester onto `fsExt` (2-4 wk): about 3-4 months. A cheap first check: prove
  minibolt refines the arm's per-file crash relation (1-2 wk).

## Related, on lean

- The WAL crash spec (W4a, W4a.1, W4a.2, W4b; W4c paused): `GooseLang/Ext/AbsDisk/`,
  `Proof/go_etcd_io/etcd/server/v3/storage/Wal*.lean`, `notes/decisions.md` "WAL ..." entries (including
  the review checklist every crash axiom should pass), `notes/wal-w4c-handoff.md` ("Paused").
- The crash ladder and restart track: the restart Scope's crash-ladder section, `notes/restart-vs-crash.md`.
