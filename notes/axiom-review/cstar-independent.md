# Option C★ (bbolt meta poison, `db`-scoped crash premise, restated `dbCrash`): independent review

Review 2026-11-26, `axiom` skill (`.claude/skills/axiom/`), adversarial and independent of the author's
argument. Code base: `origin/etcd-safe-crash-r6/2026-11-26` @ 8cdf5ff75f. bbolt fork at its pin `2f6fcff`
(`github.com/upamanyus/bbolt@v0.0.0-20261125221737-2f6fcfff7e4b`). etcd fork: `server/v3@...251a430ce042`
(`examples/go.mod`). Two fork diffs were reviewed: the open-poison diff and the combined tails diff (neither
is in the repository). The simulations and measurements below were run outside the repository.

## Verdict: SOUND WITH FIXES

The three trusted pieces together are sound **for etcd's programs**:
- No real crash image of etcd's member program is excluded, beyond a chance FNV-64a coincidence
  among bytes bbolt computed. The poisoned checksum counts as such bytes.
- C★ also makes the bbolt premise independent of the shape of a tear (prefix, old-prefix,
  new/old/new, page migration). The premise's current docstring argument has no such independence.

The premise is **false for a generic program** that names a file `db` and writes its own bytes
there. That is acceptable only because `etcdFsSem` is applied to etcd's programs alone, which I
checked. No counterexample exists against etcd. The fixes are F1 to F4 below: three are documentation
or lemmas, and one is a proof obligation. The fork diffs need no change for soundness.

## What the diffs do, and where they differ from the description of C★

The open-poison diff: `repairMetaPages`/`poisonInvalidMeta` in `db.go`. It runs inside
`if !db.readOnly && (!db.NoSync || IgnoreNoSync)`.

The sequence:
1. It runs **after** Open's existing early `fdatasync`. The description said "at the point where the early sync runs".
2. It reads pages 0 and 1 with `pread`.
3. It acts only if **exactly one** meta validates (`v0 != v1`). The description said "every slot that does not validate".
   - If both metas validate, it writes nothing.
   - If neither validates, it also writes nothing. That case is unreachable, because `getPageSize` already failed.
4. It writes **only the 8 checksum bytes**, `^Sum64()` of the kept fields. The description said the whole slot is rewritten with its fields kept. Here the field bytes get no new candidate.
5. It then runs **its own `fdatasync`**.

All of this happens before the mmap and before any commit.

The combined tails diff adds the following, and only when a tail byte (`[80, 4096)` of either meta page) is nonzero:
1. It zeroes the 4-byte magic at `getPageSize`'s probe offsets 1024+16 and 2048+16. These writes are in the same crash window as the poison, which is then synced.
2. It then writes the zero tails `[80, ps)` of both pages from a separate zero buffer, and syncs again.

The tail writes never cover meta bytes 16..80. So the hazard I had anticipated (a whole-page rewrite from a stale buffer undoing the poison) does not exist. In etcd's runs the tails are always zero, because bbolt writes meta pages from zeroed page buffers. So this branch never fires there.

## (a) Does `W1 ∧ BoltCrashDb` exclude a real crash image?

**etcd's member program: no**, beyond a chance FNV-64a coincidence.

Which inodes can be named `db`. I checked the fork sources at the pin:
- **The datadir's `member/snap/db`** (`storage/datadir/datadir.go:23`). It is written only by bbolt, opened writable and syncing (`dbOpts`).
- **The snapshot install's `<idx>.snap.db`.**
  - `SaveDBFrom` copies the bytes received from the leader (bbolt's `WriteTo` output) with `io.Copy`.
  - It `fsync`s before the rename and syncs the directory (`snap/db.go`).
  - `openSnapshotBackend` then renames it to `db`.
- **Defrag's `db.tmp.*`.**
  - It is opened with `NoSync = true` (`backend.go:534`).
  - `finishDefrag` calls `tmpdb.Sync()` before `Close` and the rename (`backend.go:581`).

So an inode that a crashed durable tree names `db` is one of two things:
- bbolt's syncing file;
- a file whose bytes were all synced before the rename onto `db` entered the metadata log, which makes every candidate stamp 0. Then `BoltCrashWhole` holds trivially, with n = m = 0.

For bbolt's syncing file, the argument does not depend on the shape of a tear:
- Each meta byte has at most two candidates between syncs: stamp 0 (the slot as of the last sync) and the one in-flight write `w`.
  - `Tx.Commit` syncs between a slot's writes, and the slots alternate.
  - The poison is synced before the first commit.
  - `init` syncs.
  - The tail writes do not cover meta bytes.
- The stamp-0 slot is either a valid meta written by bbolt, or poisoned. A torn slot left by a crash is poisoned by the next writable Open before anything writes over it.

Now take any per-byte mix of stamp 0 and `w` that validates:
- **Fields equal to `w`'s by value.** The premise holds with n = w, since every checksum byte is as of 0 or w, both ≤ n.
- **Fields equal to stamp 0's.**
  - Stamp 0 valid: the checksum equals `fnv(F0) = c0` byte for byte, so each byte is as of 0. The premise holds.
  - Stamp 0 poisoned: no poison byte equals the needed byte, so all 8 come from `w`. That means `fnv(F_w) = fnv(F0)`, a collision between two field strings bbolt wrote.
- **Fields a mix of the two.** Validation needs `fnv(G)` to equal a mix of two checksums bbolt computed: a chance coincidence (about 2^-64 per image).

What about the defrag tmp file before it is renamed onto `db`? It has several unsynced metas per slot (mix B on C), but it is not named `db` until it is synced. If its rename is kept by a crash, its data is synced.

Initial state: `FsInit` allows a `db` that is already on disk, for example one with a torn, almost-valid slot from before the model's run. That is stamp 0, and the first writable Open poisons it, so C★ covers this case too.

**A generic program: yes, it excludes real images.** Here are two counterexamples. Each uses a file `d/db` with page 0 = header plus a meta (F0, c0) synced, file size settled, and the directory synced.
1. **Mix B, measured on C** (`notes/axiom-review/fs-v2-r6/e2e/README.md`, run `B1`: mixed images at any byte, including sector 0, with aligned buffers).
   - The program does `pwrite` (F1, g) with g ≠ fnv(F1), then `pwrite` (F2, fnv(F1)) with F2 ≠ F1, and does not sync.
   - The image takes the fields from write 1 and the checksum from write 2. It validates.
   - The premise needs checksum bytes as of m ≤ 1, that is g or c0. Neither matches, so the image is excluded.
2. **Tear A, one write.** The source buffer crosses a memory page at slot byte p (Go `[]byte` alignment is 1). The (e) measurement below shows that even an aligned source can be cut at an arbitrary byte.
   - The program pre-syncs a checksum c0 = fnv(N[0..p) ++ F0[p..56)).
   - It then writes fields N and an arbitrary checksum in one `pwrite`.
   - The new-prefix image validates with mixed fields, which the premise excludes.

**Is `etcdFsSem` applied only to etcd's programs?** Yes.
- `grep` finds `etcdFsSem` and `etcdCQ` only in `examples/lib/etcdstart/*`, `examples/mvccfull/*`, `examples/etcd/leaseexpiryN/*`, `examples/etcd/dist/**` and `Net/Statement/Dist*` (under `Proof/github_com/mit_pdos/etcd_grove/`, and `Net/Statement/` for the last).
- Crash steps occur only for the dist members (`Net.CrashBootWpGT etcdCQ ...` in the dist boot files, for example `examples/etcd/dist/BootBad.lean`), whose program is `server.Main` (etcd).
- `mvccfull` and `leaseexpiryN` have no crash steps, so the relation is never used there.

**The scope is a property of the program, and nothing states it** (fix F1).

## (b) Crash sequences with the fork change

Scenarios tried by hand against the code as written (under the per-byte crash, which covers every tear shape):

| scenario | result |
|---|---|
| A crash between the poison write and its sync | The fields are unchanged and the checksum bytes are T (the torn ones) or ~fnv(F). Validation needs every byte equal to fnv(F). Poison bytes never are, so all 8 would have to come from T, and T ≠ fnv(F). **Never validates**: the slot stays invalid, and the next Open poisons it again. |
| The poison write itself torn (an 8-byte source sub-slice, which can cross a memory page) | Same as the row above: any mix of T and the poison. |
| Repeated crashes: crash → poison → commit → crash → ... | The stamp-0 slot is valid or poisoned at the start of each generation. Each crash is one of the two-candidate cases of (a). |
| Composite tears (new/old/new, old-prefix, migration cut) | Covered: the argument above takes any per-byte mix of the two candidates. Three candidates on one slot need two unsynced writes to it, which a syncing bbolt never makes. |
| A redo of the dead commit with the same fields (F_w = F) | Fields as of w. Validation needs the whole checksum from w. The premise holds. |
| A redo with other fields that leaves fields F (dead) and a checksum taken from w and the poison | Validation needs fnv(F_w) = fnv(F): a collision. Without the poison, each wrong byte of T is fixed with probability 2^-8. That is the revive scenario the poison closes. |
| Three generations: G1 = a mix of F_a and F_b, poisoned; the redo's mix brings back F_a | Validation needs every checksum byte to equal c_a, taken from ~fnv(G1) or c_b. Each byte matches by chance (about 2^-7), so about 2^-56 in total. A chance coincidence among bytes bbolt computed. No structure links them. |
| The two slots | Only the invalid slot is written; the valid one is untouched (the test checks this). Both invalid: `getPageSize` fails before the poison, and the file is left as it was. |
| Open's ordering against its early sync | The poison comes after the early sync, so it never shares a crash window with an earlier process's unsynced writes (for example a NoSync file). Correct. |
| Ordering against tail zeroing (combined diff) | Poison and probe-magic zeroing → sync → tails → sync. The tails exclude bytes 16..80 and use a fresh zero buffer. A crash in any window leaves the meta bytes poisoned or as before, and every probe invalid. |

Simulation (a script, not in the repository; scaled-down slot: 6 field bytes and 2 checksum bytes, so the chance baseline is 2^-16):
- A torn first crash, then a redo with other fields, then all 256 per-byte mixes of the second crash.
- **Without the poison**: 0.19 % of trials have a violating mix, and the mean violating share is 5.8e-5.
- **With the poison**: 0.03 % and 9.4e-6. The baseline is 1.5e-5.
- At real size (8 checksum bytes), a torn slot with one wrong byte is revived with probability 2^-8 without the poison, against about 2^-64 with it.
- A second simulation, a chain of 6 generations with random mixes, gives the same picture.

## (c) Is the `db` scope by the crashed durable tree well-formed?

- **Which tree.** The scope reads `st'.fs.treeDur`. In `crashRest`, `V' = (st'.fs.treeDur, [])`, so `hN : DbNamed V'.now i0` is the same predicate at the very crash that `Q` constrains. Well-formed.
- **Renames onto `db`, and directory-sync windows.** Whether the snapshot install's or defrag's rename is kept or dropped, the inode the crashed tree names is bbolt's syncing file, or a synced file (see (a)). The scope depends only on the crashed tree, so a rename that is not durable is handled.
- **Hard links.** The model has no `link` operation (`MetaOp` is create, mkdir, remove, rename). `TreeWf`'s last clause gives each node one name, so an inode can be named `db` at most once.
- **Inode reuse.** None: `nextIno` is kept across a crash, and an unnamed file is dropped.
- **Several directories with a `db`.** `∃ j` covers every directory. That is sound for etcd, where only `member/snap/db` is ever named `db`; it is a program condition (F1).

## (d) Satisfiability

The relation is satisfiable from every reachable state, but this is **not proved today**:
- `boltCrashWhole_exists` is stated `∀ I, ∃ st''`, so it cannot be used when I depends on st''. Its proof, however, does not use I: `durCrash st st'` satisfies `BoltCrashWhole I` for every I, so `DbNamed (durCrash st st')` works too.
- `durCrash` keeps the crash's tree. W1 holds there, because accepted frames lie in the file contents, where `durFile` equals `valAt · 0`.
- `W1Sat`'s hypothesis (`∀ b`, past the size included) is stronger than what `durCrash` gives. A direct proof is needed (F3).

## (e) The page-migration caveat: measured, without root

A test program (C, not in the repository). A writer thread overwrites page 0 of an ext4 file (`/`, `/dev/root`, Linux 7.0.0-1014-aws), using one 4096-byte `pwrite` from a **page-aligned** anonymous source page, alternating the values 0xAA and 0xBB. An observer thread reads the page through a `MAP_SHARED` mapping and times every two-valued state. It records the cut once a state has stalled for 20 µs or more.

The mover thread moves the source pages without root: in a loop, it splits their 2 MiB region (`MADV_DONTNEED` of another page in it) and collapses it (`MADV_COLLAPSE`). Collapse uses the same kernel path as migration: the PTEs are cleared and the TLB flushed, the pages are copied to a new physical page, and the mapping is restored. Each run lasted 30 s.

| mode | writes | collapses | stalls ≥ 50 µs with the cut strictly inside the page |
|---|---|---|---|
| no mover | 25.7 M / 26.0 M | 0 | 8 / 19 |
| mover on another 2 MiB region | 26.5 M | 9,591 | 43 |
| mover on the source's region | 24.7 M / 22.8 M | 24,966 / 8,701 | **1,594 / 999** |

The stalls under the mover last 65 to 262 µs (histogram mode). The cuts fall all over the page; 989 of 999 are not multiples of 64.

**Mechanism.** The TLB-flush IPI arrives in the middle of the copy (`rep movsb`). The next source access then faults with page faults disabled, and the copy stops at that byte. `ext4_da_write_end` commits the prefix of the uptodate folio and unlocks it. `fault_in_iov_iter_readable` then sleeps until the move ends.

This is exactly the window of the repo's mechanism A (`notes/axiom-review/fs-v2-r6/e2e/README.md`), in which a writeback writes the page prefix-torn. **Yes: a page-aligned source can be cut at any byte.** What was not measured is the on-disk image: that needs dm-log-writes and root.

**Rate in ordinary operation.**
- Repo run `S0` (aligned buffers, forced compaction loop): no mid-page cut and 24 cuts at byte 0 in 1.5×10^8 writes.
- The ratio of copy time (about 0.2 µs) to the migration window (tens to hundreds of µs) predicts about 0.1 mid-page cuts in that run. So the rate is roughly 10^-9 per write under heavy compaction.
- khugepaged collapsing a THP-enabled Go heap is a second natural trigger.

**Consequences.**
- These are new-prefix tears, which the current `BoltCrashWhole` already allows.
- Combined with B (old-prefix/new/old/new shapes, no stable pages), they make "a bbolt meta page does not tear on C at all" (CrashPremise.lean) false. That docstring argument must go.
- C★'s argument does not need it.

## (f) Fixes

- **F1 (trusted docstring, `Proof/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart/FsExts.lean` `etcdCQ`/`etcdFsSem`, and the trust list).**
  - State the program condition: every file that a crashed durable tree names `db` is either written only by the fork's bbolt opened writable and syncing (with the Open poison), or was fully synced before its rename onto `db` was logged.
  - Record the generic-program counterexample from (a).
  - State that `etcdFsSem` with crash steps is for etcd's member program only (today: dist members; `mvccfull` and `leaseexpiryN` have no crash steps).
- **F2 (trusted docstring, `Spec/go_etcd_io/bbolt/CrashPremise.lean`, "Why it is true").**
  - Replace the prefix-tear and page-aligned-buffer argument with C★'s: at most two candidates per meta byte between syncs; the stamp-0 slot is valid or poisoned; any per-byte mix that breaks the premise validates only on an FNV-64a coincidence.
  - Delete "a bbolt meta page does not tear on C at all", citing the measurement in (e).
  - Cite the fork's `repairMetaPages`/`poisonInvalidMeta` and its sync order.
  - Replace "the premise holds there up to an FNV-64a collision" for the defrag NoSync case with: never named `db` while unsynced.
- **F3 (lemmas, no trust).**
  - Add `boltCrashWhole_durCrash (I) : BoltCrashWhole I st (durCrash st st')`.
  - Add `etcdCQ_exists : CacheOk st → MachineCrash st st' → ∃ st'', OsCrash st st'' ∧ etcdCQ st st''`, proving W1 at `durCrash` directly rather than through `W1Sat`.
- **F4 (proof obligation for the restated `dbCrash`).** `dbCrash` is now proved in `backend/CrashLaws.lean`, and that proof passes a global `∀ st st', Q → BoltCrashWhole (·=i0)` to `boltCrashRec_crash`. That hypothesis does not follow from `BoltCrashDb`. The proof has to take the specific crash out of `crashRest` (where `V'.now = st'.fs.treeDur`, so `hN` gives `DbNamed st' i0`, and `BoltCrashWhole` is antitone in `I`). For example, use a `crashRest` monotonicity lemma to `Q' := Q ∧ DbNamed · i0`.

The bbolt fork changes need no fix for soundness. One optional item for the fork alone:
- Without the combined diff's probe-magic zeroing, a crafted file with a meta-looking tail at offset 1024 could make `getPageSize` pick 1024 when slot 0 is invalid.
- This never happens in etcd.
- The combined diff handles it; prefer that diff if the tails change lands anyway.

## Not tried

- The on-disk confirmation of (e). It needs root, dm-log-writes and bpftrace, as the repository's e2e script does.
- A Lean proof of F3 and F4.
- A Go-level test of the poison under a real power loss.
