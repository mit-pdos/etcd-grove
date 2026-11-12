# Rung 3 Freeze review (2026-11-12): findings of the three lenses (axiom, spec, LinuxFs comparison)

## Lens verdict: NOT READY: one blocker, and its fix is small. The fork's D7 `initTorn` (4f08974e) is narrower than decision D7. As a result `Open_kv_trk`'s `¬ dbOpenOk` error arm is false under the approved P4, and also under the per-byte crash rule; a test shows it. Apart from this the bolt arm agrees with the LinuxFs per-byte model and assumes no more than it does. Recommendation: fix D7 to match minibolt's proved rule, then proceed with the trusted arm and record the convergence path as a gate. Do not wait for a merge.

I compared the rung-3 bbolt arm with the LinuxFs per-byte model (GooseLang/Ext/Fs/Impl.lean, notes/fs-semantics-v2.md, minibolt's proved bootCrashSafety, notes/bbolt-port-plan.md, notes/walfs-ext-plan.md). I ran one Go check on a copy of the fork at 4f08974.

(1) Contradictions. The per-byte model contradicts exactly one claim: that an interrupted init reads as ∅, which Open_kv_trk's ¬dbOpenOk error arm relies on. A per-byte old/new mix of meta 0 (magic new, checksum old) is allowed by the per-byte rule and by the approved P4. The fork's initTorn refuses it ("version mismatch" or "checksum error" at every later start). That is B1, and it is narrower than D7 as decided; minibolt's proved rule is "re-init when neither meta validates". Everything else agrees:
- `boltImg` (the last commit or the one in flight) follows from P1/P5, which is minibolt's P1, plus copy-on-write onto pages free in N.
- Commit's error arm keeping the flight agrees with the page-cut rule, which applies only to a call's result.
- `named` and BoltNamed are weaker than ext4's whole-journal directory fsync. Both models let a file fsync commit no name.
- "Synced bytes survive a write elsewhere" holds in both.
- The arm uses only the fsync(2) contract and assumes nothing specific to ext4.

(2) Which assumptions are stronger. On byte values the arm's world is weaker (P4: anything) than per-byte (each byte old or new). On directories it is weaker: POSIX directory fsync with durable ancestors, against ext4's commitAll and journal order. It is not tied to configuration C. On kills it is much weaker: LinuxFs assumes a supervisor sync before any restart, which assumes away §1.6's kill-then-power bug, while the arm models it. So the arm's claims are stronger than any LinuxFs result on that axis. The arm rests on P5 just as minibolt rests on P1.

(3) Path to replacing the arm with a proof, with estimates:
- (a) fsExt gets a process-kill crash (trusted Impl change, semantics example, review, CacheOk) and its clients are re-proved under it, or the kill is made a selectable filter. About 1-2 weeks. minibolt will probably need bbolt's Open sync.
- (b) Finish the paused real-bbolt port (bbolt-port-plan §7: WriteAt past EOF, chunks, then 62 files and 20.5k lines, 38 file-name files, build sweeps). About 2-3 weeks.
- (c) A crash invariant for real bbolt modelled on minibolt (CrashSt, cfInv/csInv, P1). The candidates must be carried in Inv/Store, plus the free-page and pending argument and crash proofs for Open/init/initTorn/sync/Commit. minibolt's crash side is about 17k lines for a small program, so expect about 6-10 weeks.
- (d) A bridge: either define the bolt arm as an abstraction of FsState and prove a refinement (fsExt implements the BoltOpen/Begin/Sync/Named steps and boltCrash), or move the whole tester onto fsExt, which also needs the WAL on Fs (walfs plan). About 2-4 weeks for the refinement.

Total: roughly 3-4 months for the bolt arm alone. A cheap first milestone (about 1-2 weeks) is to prove that minibolt refines the bolt arm's per-file crash relation over the per-byte model; that checks the arm's shape against a proved model early.

(4) Recommendation: proceed with the trusted arm now; do not wait for a merge, since the per-byte route to real bbolt crash safety is months away and its restart assumption would hide the bug rung 3 is about. Before R3-4:
- fix the fork's initTorn (B1) and move the pin;
- add a byte-mix image mode to crashsim and rerun the controls (M1);
- record the convergence path, with ProcKill in fsExt as a prerequisite, as gate G4 in notes/decisions.md (M2);
- fix the minor points m1-m3: BoltOpen commits only on a successful fdatasync, P4/P5 wording, G3 widened to rename and unlink.

The only file I wrote is the scratch test /shared/tmp/coord-81/rung3-review/linuxfs/bbolt/perbyte_review_test.go, in a copy of the fork; I did not touch the worktree.

### B1 (BLOCKER)

(1) A per-byte crash image contradicts the arm's "zero metas read as ∅" claim and Open_kv_trk's error arm (err ≠ nil only under ¬dbOpenOk). The per-byte rule (Fs/Impl.lean header, "each byte any one of its candidates, independently"; the device leaves each byte old or new) and the approved P4 ("a byte written but not synced reads back as anything") both allow the following state. A power loss falls between init's two fdatasyncs. Meta page 0 comes back with its first bytes new (page header, magic, possibly version) and its checksum old (zero); meta 1 stays zero; pages 2-3 were synced. The fork's D7 `initTorn` (bbolt db.go:772-795 at 4f08974) refuses any file whose meta carries the magic number. `metasZero` is false and `getPageSize` fails, so `Open` returns an error on every later start. The arm says the file is `absent`, or a crash image of `⟨∅, none, _⟩` (freeze §2.1 lines 99-100, `boltOpened .absent`), so the next Open must succeed. The fork's own nonissue says this case stays open ("A file whose meta has the magic number but a wrong version or checksum still fails to open"). The random-sector garbage tester never draws it (the magic matches with probability 2^-32). Decision D7 as recorded (freeze lines 537-538, 554: "re-runs init when no meta validates and the file is exactly init's four pages") is broader than the commit. minibolt, which is proved crash-safe over the per-byte model with P1 (LinuxFs bboltfs `bootCrashSafety`), re-inits whenever neither meta validates (examples/osfs/bboltfs/minibolt.go:71-93). A kill during init's meta pwrite that leaves a mid-page prefix in the page cache (the Fs header says a killed mid-copy write can do this) reaches the same state without a power loss.

**Evidence:** Test on a copy of the fork at 4f08974 (/shared/tmp/coord-81/rung3-review/linuxfs/bbolt/perbyte_review_test.go, TestReviewPerByteMixedMeta): init's four pages, then meta 0's first `cut` bytes new and the rest old (zero). Results: cut 20 gives `Open: version mismatch`, cut 40 gives `Open: checksum error`, cut 80 (whole meta) opens. TestOpen_InterruptedInitTornMeta passes, because it only garbles with bytes that lack the magic number. Code: db.go:280 (`info.Size() == 0 || zero || db.initTorn(...)`), db.go:784-787 (magic check). Freeze: lines 99-100, §3.4 error arm, §5 row "BoltOpen on absent / zero-length file reads ∅".

**Fix:** Fork: drop the magic condition from `initTorn`. Re-init when the file is exactly 4 pages, neither meta validates and pages 2-3 are init's, which is what D7 says. A database that has committed is larger and synced its size before its meta (freeze §1). Alternatively adopt minibolt's rule, which is proved over the per-byte model. Add test cases for a meta with a valid magic and a bad version or checksum. Move the pin and re-check Open's proof (`DB.initTorn.spec_own`). Update the nonissue's last paragraph and freeze line 99. Add an image mode to the tester (below, M1) so the evidence covers this class.

### M1 (MAJOR)

Evidence gap (questions 1 and 2). crashsim (examples/etcd/mvcccrash/crashtest/crashsim/model.go:12, 465-532) keeps whole 512-byte sectors: old, new, a prefix tear, or random garbage with probability `-garbage`. It never produces the per-byte rule's crash images: an unsynced sector whose bytes are each old or new, independently. Those images are the realistic ones, measured on configuration C (mechanisms A and B in notes/fs-semantics-v2.md). They are also the ones that defeat structural checks such as the magic number (B1). Random garbage almost never reproduces a structure, so the tester's 0-violation rows say nothing about this class.

**Evidence:** crashsim model.go: `mode := 0 // 0 new, 1 old, 2 random per sector, 3 prefix tear`; garbage is `make([]byte, sector)` plus random bytes. Freeze §5.1-5.2 counts no byte-mix images. The fs-v2 measurements are in notes/fs-semantics-v2.md ("Byte-level crash candidates").

**Fix:** Add a crashsim mode `bytemix`: for each unsynced changed sector, each byte independently takes one of its candidate values (at minimum the last synced value and the page-cache value; all writes since the last sync in general). This is Fs's `CrashFile`. Rerun the §5.2 controls with it at the D7-fixed pin, and run init-targeted images of a fresh db's first incarnation.

### M2 (MAJOR)

(2) The restart assumptions of the two models are incompatible, so the convergence path must change the Fs model. Record this now. LinuxFs assumes restarts happen only after a machine restart or after a supervisor `sync(2)` (Fs/Impl.lean header, "Restarts"; fs-semantics-v2.md "Restarts are machine crashes"; V6 superseded). The bolt arm models a kill without sync, `⟨last, some D⟩`, and its sequences with power loss. That is exactly where §1.6's bug and the fork's Open sync (c5a6065) live. On this axis the arm is the weaker world assumption, and the claim of etcd_mvcccrash is the stronger one. A proof over today's per-byte model would assume the bug away: under its restart assumption minibolt needs no Open sync, and real bbolt would not either. Replacing the trusted arm with a proof therefore first needs a process-kill crash in fsExt: FsState kept, the change in flight landed as any announced prefix per byte, candidates and size bounds kept, metaLog uncommitted, ProcState dropped. It also needs the existing clients (minibolt, walfs, crashlog) re-proved under it, or the kill relation made a selectable filter. minibolt would likely then need the same Open sync. That would confirm §1.6 from the other side.

**Evidence:** Fs/Impl.lean, header paragraph "Restarts: the program restarts only after a machine restart, or after ... a sync(2) has made everything it left durable". Freeze §0.2 and §2.1 `boltCrash`'s second disjunct. scope.md P7.

**Fix:** Add a convergence entry to notes/decisions.md, and to notes/fs-semantics-v2.md under "Open": a ProcKill crash is a prerequisite for any proof that replaces the bolt arm. List it as gate G4 next to G1-G3. Say in the mvcccrash theorem's documentation that its kill-then-power claim is outside what LinuxFs results claim.

### m1 (MINOR)

`Open_kv_trk`'s body (§3.8 step 2, and "after step 2 (the sync failed or later): Q dropped") commits `"BoltOpen"` at the fdatasync whatever its result. In both the per-byte model and P1, a failed fdatasync makes nothing durable. A body that commits on failure claims `⟨read, none⟩` while the disk may still revert to the old last commit, the kill-then-power case. Under the closed theorem's dbOpenOk the error arm is unreachable, so nothing is lost. The body still does not model Go, and §3.5 step 4 already handles the same situation correctly for Commit.

**Evidence:** Freeze lines 375-381 (§3.8), compared with line 392 (Commit: "an fdatasync error instead: return with Q₁ (U₂ dropped)"). Fs/Impl.lean: "a failed one changes nothing".

**Fix:** State that the update commits only when the fdatasync returns 0. On a sync error the body returns with U unopened ("committed or not" in the post still covers the client's side).

### m2 (MINOR)

P4's justification says "(sector-atomic writes, no read-modify-write corruption)". The C measurements refuted sector atomicity, and the per-byte model dropped it. The claim P4 makes (a synced byte not rewritten keeps its value) still holds under the per-byte model, through its device assumption that every byte is old or new and never garbage. Only the stated reason is wrong. P5 under "arbitrary" bytes should also exclude garbage that reproduces a stale well-formed meta, not only torn ones; minibolt's P1 shape (a validating slot is the slot as of one change, `valAt`) says this exactly.

**Evidence:** /shared/tmp/restart-scope/crash-design-powerloss.md:334-335; notes/fs-semantics-v2.md "Byte-level crash candidates" and the environment's superseded "Sector atomicity"; LinuxFs bboltfs BootP1.lean.

**Fix:** Restate P4's reason as "each byte old or new" (the per-byte device assumption), and P5 in P1's form. Neither changes the approved meaning; flag it to the user only if they read it as a change.

### m3 (MINOR)

The arm is keyed by path. The per-byte model's reason for inodes (V2: an fd follows its file across rename and unlink; a crash can pair an old name with new contents) means a path-keyed arm is sound only while nothing renames or unlinks a tracked path. Rung 3 has neither (G1 covers rung 4's OpenSnapshotBackend rename). Gate G3 should list rename/unlink of a tracked path, by any trusted model, as excluded, not only bolt steps.

**Evidence:** notes/fs-semantics-v2.md V2; freeze §2.4 ("Who else names paths") and §4 G1/G3.

**Fix:** Extend G3: no trusted model may rename, unlink or truncate a tracked path. Note that rung 4's rename needs either inode identity in the arm or C6's conversion at the rename.

> Verifier: refuted=False. I could not refute B1. Everything I checked holds.

(1) The code. In the fork at 4f08974 (/shared/tmp/bbolt-fix/bbolt/db.go), Open re-runs init only on `info.Size()==0 || zero || db.initTorn(size)`. `initTorn` returns false whenever either meta page carries common.Magic. Its own docstring says: "A file whose meta has the magic number but a wrong version or checksum still fails to open, as before."

(2) Reproduced. I ran the test on a fresh copy of the fork at 4f08974 (/shared/tmp/coord-81/rung3-review/skepticB1/bbolt/perbyte_review_test.go). The image is init's four pages, with pages 2-3 synce

> Verifier: refuted=False. The finding holds. It is also more than a coverage gap: it hides a real counterexample.

1. The code says what the finding says. /shared/etcd-grove-rung3/examples/etcd/mvcccrash/crashtest/crashsim/model.go:465-532 picks one mode per image (`mode := 0 // 0 new, 1 old, 2 random per sector, 3 prefix tear`). Every mode chooses a whole 512-byte sector version from `cands`. The only other image is whole-sector random garbage (`d = make([]byte, sector); rng.Read(d)`). No mode mixes the bytes of a sector's candidates. Freeze §5.1-5.2 counts only posix, ordered, garbage, kill and targeted images.

2. T

> Verifier: refuted=False. The facts check out. The restart assumption is in /shared/etcd-grove/GooseLang/Ext/Fs/Impl.lean:30-36 on lean: the program restarts only after a machine restart, or after the old process exited and a sync(2) made everything durable, so the model has machine crashes only. notes/fs-semantics-v2.md:182-190 ("Restarts are machine crashes", 2026-11-06) says the same, and it marks V6, a crash on process restart, as superseded (line 134). The crash-rung3 worktree branched from lean at b4f0711091, before LinuxFs landed, so neither file is in it.

The Freeze's boltCrash (freeze-r3-3.md:127-130) has the

## Lens verdict: NOT READY

I reviewed the package read-only and built nothing. The one Go run was a test in a copy of the bbolt fork at 4f08974 (/shared/tmp/coord-81/rung3-review/axiom/bbolt/zz_review_test.go). Verdict: NOT READY, because of two blockers.

B1 is the W4a round-2 B-1 bug class again. The new tracked-file axioms do not require durable's reservation. While durable is unreserved it may write any name, the hidden tracked path included. A program that writes a valid bbolt image to `snap/.db` and then calls Open_kv_trk gets a ghost read of empty data while Go reads the image.

B2 is that the D7 fork fix is incomplete, as Go shows. `initTorn` checks the magic number and init's page headers, not whether a meta validates. Six images that a power loss can leave under the approved "arbitrary unsynced bytes" assumption all fail Open at the fork. The nonissue admits one of them; the package itself claims D7 closes the gap. Open_kv_trk's claim (an error only under `¬dbOpenOk`) therefore still rests on a false premise, by the package's own §5.1 standard.

Majors:
- M1: the untracked witness (`dbUntracked`) holds only if no `fileHolds` names a tracked path (gate G1), and nothing enforces that. `goose_adequacy_start_files` is generic over the extensions, so a crash-free program can be refuted without any crash.
- M2: Open's commit point is not tied to the fdatasync returning 0, and the §3.8 body commits even when that sync fails.

Minors:
- the body's justification should cite `flock`;
- the D7 text does not match the code;
- the `osFsExt` gate is missing from §2.4;
- the fsync-error case (`fsyncgate`) should be scoped;
- the BoltFile docstring needs updating.

What survived:
- the crash relation over power loss, kill and both in sequence, checked against the fork's commit order, the meta alternation and the freelist with NoFreelistSync=true;
- the error arms of Commit;
- the read-only attack, which `OptsM.ok` blocks with `readOnly = false`;
- Close, which writes nothing;
- a second database handle, which deadlocks on `flock` and is not a counterexample;
- the semantics of syncDir;
- the review checklist: no post gives a past-state fact, `named` is raised only by the client's own atomic update, and every post has a realizing body.

I did not try: the Lean proofs of the counterexamples; crash images driven by the driver for B2, which used constructed images instead; and the WAL/bolt crash outcomes taken together, beyond arguing that the product relation contains the real joint outcome.

### B1 (BLOCKER)

The new tracked-file axioms do not require durable's reservation, so the durable extension can write the tracked file unseen by the bolt arm: the W4a round-2 B-1 bug class again. The package argues (freeze §2.4) that durable never names a tracked file because hidden names are excluded in reserved mode. But only the WAL axioms require the reserved mode: `walAreaOk r = walArea r ∗ durableResvD r`. Open_kv_trk's precondition has no reservation. Unreserved, durable allows any name (`durableNameOk none _ = True`). Counterexample shape: Main (1) writes a valid bbolt image whose bucket "k" exists to `/r/.db` with durable's whole-file Write, without reserving; (2) calls `bolt.Open("/r/.db")`; (3) panics if `tx.Bucket("k") != nil`. Start: `s0.bolt = {/r/.db ↦ absent}`, which meets `absDiskInitOk`. The proof commits Open_kv_trk's atomic update on `absent`, receives `Q (boltRead absent) = Q ∅` and `ownDB db γ ∅`, and the kv axioms then return a nil bucket. Go opens the image and panics. A durable file written at the path before Open also stops a later reservation, so the program simply never reserves.

**Evidence:** freeze-r3-3.md:192-193 ("durable (reserved mode, which the WAL functions and TouchDirAll already require)") and :289-295 (Open_kv_trk's precondition: no reservation); GooseLang/Ext/Durable/Specs.lean:74-76 (`durableNameOk none _ = True`); Proof/go_etcd_io/etcd/server/v3/storage/WalDisk.lean:125-126 (the WAL axioms take `durableResvD`); GooseLang/Ext/AbsDisk/Impl.lean:48-56 (W4a: rung 3 "must first extend the reservation"); notes/decisions.md:34764ff (W4a round 2, B-1: the same refutation for the WAL).

**Fix:** Add `durableResvD r` (for some r) to Open_kv_trk's precondition; reserved names never hide and `boltPathOk` requires a hidden last element. Commit and Close then inherit the protection, since a reservation persists across crashes. State the same for `osFsExt` (see m3): either a premise of the axioms, or a recorded gate that no closed theorem combines `osFsExt` with tracked bolt keys.

### B2 (BLOCKER)

D7's `initTorn` does not recover every image that a power loss inside `init` can leave under the approved "arbitrary unsynced bytes" assumption. Open then fails for bbolt's own reasons, while Open_kv_trk claims an error only under `¬dbOpenOk`. The package's own §5.1 calls exactly this a blocker: "a fork fix is needed before R3-3's text can stand". The code re-initializes only when the file is exactly 4 pages, neither meta has the magic number, and pages 2-3 carry init's headers. §7 and the nonissue's Proof paragraph instead say "no meta validates". Go at 4f08974 (Open with NoFreelistSync=true), all six cases fail:
- A: 4 pages of garbage (power loss before init's first fdatasync; every page unsynced) → invalid database;
- A2: garbage metas plus a garbage page-3 header → invalid database;
- B: both metas with the magic intact and the checksum torn (between the two fdatasyncs, per-byte arbitrary) → checksum error;
- B2: both metas with the magic intact and the version torn → version mismatch;
- C: a 2-page garbage file (size not yet synced) → invalid database;
- D: meta 0 zero and meta 1 torn with its magic intact → invalid database.
The nonissue concedes case A ("still not recovered"); the Freeze package does not mention it.

**Evidence:** /shared/tmp/bbolt-fix/bbolt/db.go:772-790 (`initTorn` tests the magic and the page headers), :702-758 (init: two fdatasyncs); test /shared/tmp/coord-81/rung3-review/axiom/bbolt/zz_review_test.go (`TestReviewInitResidual`, all six cases print "Open FAILED"); freeze-r3-3.md:99-100, :457-458, :538; nonissues/bbolt-fork-init-garbage-meta.md (Fixed paragraph: "before init's first fdatasync, with garbage in pages 2-3 as well, is still not recovered").

**Fix:** Fork: re-run init when the file is at most 4 pages and neither meta Validates (checksum included), with no condition on the magic or on pages 2-3. Why no data can be lost: once init's second fdatasync returns, at least one valid synced meta always survives (the metas alternate, and synced bytes survive sector rewrites), so "no valid meta" means init never completed. Add cases A-D to `TestOpen_InterruptedInitTornMeta`. Update §7, the nonissue and the BoltFile docstring (any file whose init never completed reads as ∅).

### M1 (MAJOR)

Option (U) is sound only under gate G1 (no `fileHolds` names a tracked path), and nothing enforces G1 across the trust base. The package says it holds today because `fileHolds` is minted only by the crash-free start. But `goose_adequacy_start_files` is generic over the extensions (`extsInitP σ.world`), so one closed theorem can both mint `fileHolds p ∅` (with `p ∈ Fs`) and start the abstract disk tracking `p` (`s0.bolt !! p = some absent`). Both hypotheses are true of a real start. Crash-free counterexample: `Open_kv(p)` gives `dbUntracked`; Put; `Commit_kv` (the arm stays absent); `Close_kv` gives `fileHolds p S`; then `Open_kv_trk(p)` from the arm reads `boltRead absent = ∅`, and a Get of a key in S panics in Go. `os.Rename` (`fileHolds src ∗ pathOwn dst`) can also move a `fileHolds` onto a tracked path.

**Evidence:** freeze-r3-3.md:241-245 and :420-421 (G1 recorded only); Proof/runtime/Start.lean:190-205 (`goose_adequacy_start_files`, generic over the extensions); Spec/os/Rename.lean:41-46.

**Fix:** Make G1 part of the trusted text: add a hypothesis to `goose_adequacy_start_files`/`dbFilesAbsent` that the abstract disk tracks none of `Fs` (or that `s0.bolt = ∅` whenever `Fs ≠ []`). Alternatively, add a checked gate script that refuses any closed theorem using both the start-files axiom and a nonempty bolt map. Extend it to `pathOwn` (`os.Rename`'s target).

### M2 (MAJOR)

Open's commit point is underspecified. §3.8 commits the update "at the fdatasync" and, on "the sync failed or later", drops Q, so the body commits `boltOpened b` (meaning: durable) even when the fdatasync failed or before it returns. A power loss during that sync, or an EIO, then leaves the arm at `⟨D, none⟩` while the disk may revert to `last`. The `¬dbOpenOk` error arm only hides this behind the premise, and `dbOpenOk`'s docstring does not list the sync. Commit's second update correctly says "at the meta's fdatasync return".

**Evidence:** freeze-r3-3.md:375-381 (Open's body, steps 2-3 and the error case); Proof/go_etcd_io/etcd/server/v3/storage/backend/InvBbolt.lean:79-86 (`dbOpenOk`'s docstring); db.go:322-333 (fork: on a sync error, `db.Close()` and return the error).

**Fix:** Commit the update only after `fdatasync` returns 0; on a sync error, return without committing (the spec already allows "committed or not"). Add Open's final fdatasync to `dbOpenOk`'s docstring.

### m1 (MINOR)

§3.8 step 3 justifies `D = boltRead b` by "the client held boltFileAt, so no step moved it in between". The client keeps the arm in an invariant and gives out other atomic updates, so it does not hold it exclusively. What actually keeps the arm unchanged between step 1's read and the commit is bbolt's `flock`: no other handle can write the path, and syncDir changes only `named`, not `boltRead`.

**Evidence:** freeze-r3-3.md:377-379; db.go:258-266 (the exclusive flock, Timeout 0).

**Fix:** Restate the argument through `flock`.

### m2 (MINOR)

D7's description in §7 and in the nonissue's Proof paragraph ("no meta validates and the file is exactly init's four pages") does not match the code (no meta has the magic number, plus pages 2-3 headers). This mismatch hid B2.

**Evidence:** freeze-r3-3.md:537-538; db.go:780-789.

**Fix:** Align the text with the code after B2's fix.

### m3 (MINOR)

§2.4 lists who else names paths but leaves out `osFsExt` (the Linux file extension, used by `examples/osfs`). W4a's docstring names it as a gate that rung 3 must close.

**Evidence:** freeze-r3-3.md:187-198; GooseLang/Ext/AbsDisk/Impl.lean:52-54.

**Fix:** Add an `osFsExt` bullet and a gate (or a premise, see B1).

### m4 (MINOR)

The fsyncgate case is not addressed. If the meta's fdatasync fails with EIO, Linux may mark the page clean while keeping the new meta in the cache. etcd then Fatals; the next process reads S, Open's fdatasync returns 0, and the arm says `⟨S, none⟩` while the disk holds N. A later commit can then reuse pages of N, and a power loss corrupts the database. The approved fsync contract ("once fsync returns 0, content as of the call durable") excludes this, but only implicitly. Commit's error arm carries no environment premise.

**Evidence:** freeze-r3-3.md:315-325 (Commit's error arm keeps the flight), :62-66.

**Fix:** State in the world assumptions' scope that no earlier writeback error is silently lost (or give Commit's error arm a `¬dbCommitOk` premise).

### m5 (MINOR)

The BoltFile docstring ("zero length or zero metas reads as ∅") and §5's row cite only the zero cases, which is weaker than what Open must handle once B2 is fixed. The tester still opens `snap/db`; the move to `.db` (D2) is due in R3-4 and is not done yet.

**Evidence:** freeze-r3-3.md:99-100, :438; examples/etcd/mvcccrash/mvcccrash.go:244.

**Fix:** Update the docstring and the §5 row after B2; move the path in R3-4.

> Verifier: refuted=False. The finding holds, but I rate it MINOR rather than MAJOR. The problem is in the prose that describes the realizing body; the axiom itself is fine.

Evidence: freeze-r3-3.md:375-376 (§3.8, Open body step 2) commits `U` "at the fdatasync". The error case at :380-381 says "after step 2 (the sync failed or later): `Q` dropped". So the described body has already performed "BoltOpen" (state `boltOpened b` = ⟨read, none, named⟩) when the sync fails, or before it returns. The fork's code shows that ordering is wrong. At db.go:322-333 a sync error leads to `db.Close()` and a returned error, so nothing 

> Verifier: refuted=False. The finding holds. Open_kv_trk's precondition (freeze-r3-3.md:289-295) has no durable reservation, and neither do Commit_kv_trk or Close_kv_trk. The WAL axioms are the only place the reservation is required, through walAreaOk = walArea r ∗ durableResvD r (WalDisk.lean:125-126). An unreserved program can write any name: durableNameOk none _ = True (Durable/Specs.lean:74-76), and wp_DurableWrite (Specs.lean:423) takes a name f with no side condition. That includes a hidden name like /r/.db, which passes boltPathOk. The durable and absDisk ghost states are independent, so nothing ties durable's f

> Verifier: refuted=False. The finding holds; I could not refute it. Checked against worktree /shared/etcd-grove-rung3 and /shared/tmp/crash-rung3/freeze-r3-3.md.

(1) `goose_adequacy_start_files` (Proof/runtime/Start.lean:190-213) is generic over `[GooseExts]`. Its only constraint on the starting state is `Hinit : extsInitP σ.world`. The package's `absDiskInitOk` (freeze:172-173) asks of `s.bolt` only that every tracked path satisfies `boltPathOk`. So one closed theorem can hand out `fileHolds f ∅` for `f ∈ Fs` and also start the arm with `s0.bolt !! f = some absent`, as long as `f` is hidden, e.g. `/x/.db`. Nothing in

> Verifier: refuted=False. B2 holds up. I checked it against the fork's code and re-ran the test.

1. **What the fix tests.** At fork commit 4f08974, `initTorn` (/shared/tmp/bbolt-fix/bbolt/db.go:772-790) re-runs init only when all three of these hold:
   - the file is exactly 4 pages;
   - neither meta has the magic number;
   - pages 2-3 carry init's freelist and leaf headers.
   It never checks the checksum or the version. `Open` (db.go:276-290) otherwise falls through to `getPageSize`, which fails when neither meta validates. D7 as decided (freeze-r3-3.md:537-538, :554) says the fix applies when "no meta validates".

## Lens verdict: READY WITH CHANGES

Read-only review through the spec/composition lens. I edited, built and committed nothing. Files checked: the package (/shared/tmp/crash-rung3/freeze-r3-3.md), the scope, the worktree /shared/etcd-grove-rung3 (AbsDisk Impl/Specs/Paths, Durable Specs/Crash, InvBbolt, the bbolt kv specs and axioms, BboltOptions/BboltOptsDefs, InvBackend, batchTx.commit, Start.lean, the mvcccrash tester and commit bdecad79b8), the W4c plan (/shared/tmp/wal-spec/w4c/plan.md, for Q1), etcd's bootstrapBackend, read_tx.go and cindex.go at c90b03b56, and the §5.2 control logs.

The bolt arm itself holds up. It is minimal: one field, four steps, and one per-file crash relation that is closed under kill, power loss and their sequences. I checked kill then kill, kill then power loss before Open's sync, a crash during init, the commit error arm, vanish with named=false, and the flock-blocked reopen: in each case reality stays inside boltCrash. It also composes with the WAL arm in one absDiskExt: the step names are disjoint, each step touches one field, BoltNamed reads `dirs` only through a lower bound, no post gives a past-state fact, and every step is the commit of an update the client handed over. absDisk already allocates fresh ghost names per generation, so the arm gets its own per-generation names for free.

On the other questions in the lens:
- **dbUntracked:** it leaves every closed theorem's statement unchanged.
- **The weakened Open_kv/Commit_kv/Close_kv:** the existing proofs can still discharge them. Only newBackend, batchTx.commit, backend.Close and axiomcx/bboltnan call them. `isBackend` is persistent and already holds the db at InvBackend.lean:1370, so the witness fits beside it.
- **Tester change bdecad79b8:** it only follows etcd's boot order and weakens no check. It adds one read; all `check(...)` lines are unchanged; the `ci0` it compares is the value Open read and synced, as before; and on a fresh db the missing-bucket read returns 0 (read_tx.go:107-113).

Changes needed before R3-4:
- **M1 (soundness gate G1):** G1 can already be broken through the generic `goose_adequacy_start_files`. A concrete program would verify and still panic.
- **M2 (missing trusted text):** D3's change to the trusted `optsAt_bool`/`optsZero`/`optsVal` axioms is not written in the package.
- **M3 (spec principles):** (U) creates a two-axiom family for each of Open, Commit and Close, and puts a stronger claim on the existing Open_kv under the same name. The principles say such a step goes to the user first (D1 was decided by etcd-grove-81 under delegation). They also say to list the collections that now rest on the stronger claim. A single axiom per function, with the mode as a gated row, would let R3-5 prove the backend once instead of twice.
- **Minors:** Open's body linearizes before the sync is known to have succeeded; the tester's area is not stated; boltPathOk should also keep the area from lying under the tracked path; the crash-start split and keep-lemma for Q1; pins and evidence provenance; the extension's name and docstrings; tcb and interface churn; the boltOwn/boltFileAt definitions should be frozen; justify or drop `noGrowSync`; the one-commit Open branch; and the LinuxFs per-byte comparison the user asked for on 2026-11-12 is missing.

No new issue or nonissue in the verified Go code was found.

### M1 (MAJOR)

Gate G1 ('no fileHolds names a tracked path') carries the whole consistency argument for D1(U): dbUntracked is what Open_kv now claims from fileHolds. But G1 can already be broken with today's axioms, not only in rung 4. goose_adequacy_start_files is generic in [GooseExts]/[GooseInterp]. It hands `fileHolds f ∅` for each f in Fs, under `dbFileAbsent e f`, whose meaning is 'touched only through the backend's and bbolt's operations with trust-boundary specs', and the tracked axioms are such operations. A crash-free closed theorem with absDiskExt (s0.bolt = {f ↦ absent}, f hidden, so absDiskInitOk holds) can then verify this program: Open_kv(f) from the start's fileHolds; Put k=v; Commit_kv (dbUntracked, the arm does not move); Close_kv (gives fileHolds f {k:v}); Open_kv_trk(f) through the AU over `boltFileAt f absent`, giving ownDB db γ ∅ (boltRead absent = ∅); then `if Get(k) != nil { panic }`. The proof shows no panic; real Go returns v and panics. The mirror case also works: hold a stale fileHolds f D while a tracked db commits, then Open_kv(f) reads D. The package says this is only rung 4's concern ('a crash theorem uses goose_crash_adequacy, which mints none'). That is true of etcd_mvcccrash_adequate, but not of the axiom set taken as a whole, which is what the Freeze freezes. It is also the case the hard rule warns about: an axiom strengthened in place 'can be false on an input the old one covered harmlessly'.

**Evidence:** freeze-r3-3.md:238-247 (U and the G1 claim), :420-421 (G1 recorded for rung 4/C6); Proof/runtime/Start.lean:53-61, 166-169 (dbFileAbsent's meaning; start_files over generic GooseExts, :183); Spec/os/Rename.lean (fileHolds dst from pathOwn dst); Spec/go_etcd_io/bbolt/Open_kv.lean (fileHolds path D in the pre); freeze :282-301 (Open_kv_trk does not consume or exclude fileHolds).

**Fix:** Make the separation structural, using D2 itself. A tracked path is hidden (boltPathOk). So require every fileHolds producer to name non-hidden paths: add `∀ f ∈ Fs, ¬ durableHidden f` to start_files' premise (or to dbFileAbsent's checked meaning); check that os.Rename's pathOwn producers, OpenSnapshotBackend (snapDBPath, backendPathOf) and snapshot.WriteTo name non-hidden paths (they do today); and say in dbUntracked's docstring that it means 'path not hidden, hence not tracked'. Rung 4 then has to revisit this together with G2 (a non-hidden member/snap/db). If you keep the review-only gate instead, state G1 as a property of the axiom set, cite start_files explicitly, and add a mechanical check in etc/ that no closed theorem with absDiskExt uses start_files, os.Rename or OpenSnapshotBackend.

### M2 (MAJOR)

D3 ('two fields in the backend's OptsM, set by newBackend from UnsafeNoFsync') needs trusted-text changes that the package does not write out. Options is an axiomatized type. `optsAt_bool` is the trust-boundary axiom saying that storing NoSync or NoGrowSync 'keeps o'. For Open_kv_trk's premise `o.noSync = false ∧ o.noGrowSync = false` to be dischargeable, that axiom has to be split so that these two stores set `o.noSync`/`o.noGrowSync`. `optsZero`, `optsVal`, `wp_optsLit` and possibly `boltOpenOptionsOk` must also carry the new fields. These are trust-boundary statements, and existing closed theorems use them through newBackend. A Freeze is the hard stop for exactly such texts. Separately, `dbTracked db path` must mean 'opened with NoSync = NoGrowSync = false', because Commit_kv_trk's two fdatasyncs depend on db.NoSync. Its docstring should say so.

**Evidence:** freeze-r3-3.md:292-293, 303-304 (D3 described in a parenthesis only), :551; Proof/go_etcd_io/etcd/server/v3/storage/backend/BboltOptions.lean:89-96 (optsAt_bool: NoSync/NoGrowSync 'keeps o'), :18-30 (the assumed list); BboltOptsDefs.lean:33-40 (OptsM, optsZero), :78; newBackend.lean:125-128 (the stores); S/storage/backend/backend.go:227-228.

**Fix:** Add a §3.x to the package with the restated `optsAt_bool` (NoSync and NoGrowSync split out as setters), the extended `OptsM`/`optsZero`/`optsVal`/`wp_optsLit`, and dbTracked's docstring carrying the sync options. List the collections that rest on the restated axioms.

### M3 (MAJOR)

(U) gives each of Open, Tx.Commit and DB.Close two trust-boundary axioms, selected by the mode witness dbUntracked/dbTracked. The package says the change is additive. But R3-5 already plans 'newBackend/batchTx.commit/backend.Close over both modes', and rung 4's server needs both modes at once: the tracked member/snap/db alongside untracked snapshot and defrag databases. So every backend proof above bbolt splits in two. PRINCIPLES 'One spec per function; special cases are instances' says a step that would start a family goes to the user first, and that a mode belongs in the state, not in a second spec. 'One spec, a gated row' gives the composable alternative. A single persistent `dbMode db m` (m : Option GoString, with an agreement law) and one axiom per function: Commit_kv's pre takes `dbMode db m` plus the two AUs gated on `m = some path` (trivial at none); Open_kv takes a source chosen by the caller (`m = none → fileHolds path D`, `m = some path → the AU`); Close_kv gives `fileHolds` only at none. This keeps every closed statement unchanged, has the same trusted content as (U), and lets batchTx.commit be proved once, parametric in m. The package also strengthens Open_kv's post under the same name (it now gives dbUntracked) without listing the collections that rest on the stronger claim. The hard rule requires that list, because `--check` does not flag a change under the same name.

**Evidence:** freeze-r3-3.md:238-254 (U/S/M; no gated variant considered), :529-530 (R3-5 'over both modes'), :536 (D1 decided by etcd-grove-81 under delegation); .claude/skills/spec/PRINCIPLES.md:82-106 (one spec per function, families to the user, strengthening in place: list the collections), :168-176 (gated row; a new mode redefines in place).

**Fix:** Either adopt the gated single axiom per function (dbMode), or add a paragraph explaining why it was rejected and put the family choice to the user. In both cases, list the tcb collections (server, mvccfull, mvccrand, axiomcx/bboltnan, ...) that rest on the strengthened Open_kv.

### m1 (MINOR)

Open_kv_trk's body (§3.8) commits the AU 'at the fdatasync' and then treats 'the sync failed' as a case after the commit. That linearizes BoltOpen (the data marked durable, flight := none) before the sync is known to have succeeded. Only the `¬ dbOpenOk` error arm makes this harmless, so the step is unfaithful in exactly the runs where the environment fails. Commit_kv_trk's body (step 4) handles this correctly: it commits U₂ only when the meta's fdatasync returns success. Committing after a successful return is always sound: between the return and the step, the relation already allows the synced state.

**Evidence:** freeze-r3-3.md:375-381 (step 2: commit at the fdatasync; 'after step 2 (the sync failed or later): Q dropped'), contrasted with :390-392.

**Fix:** Step 2: perform `"BoltOpen"` and commit only after the fdatasync at B/db.go:322-333 returns 0. If it fails, take no step and drop the AU (error arm).

### m2 (MINOR)

The package never states the WAL area that etcd_mvcccrash_adequate will use, yet the paths depend on it. Boot runs TouchDirAll on root/data, root/data/member and root/data/member/snap. W4a's DirDurable is stuck under the area, and boltPathOk requires `¬ underDir area p` for p = root/data/member/snap/.db. W4a's header also requires the area to be at or below the data directory. So the WAL tester's area (root/data/member) cannot be reused; something like root/data/member/wal works. Separately, boltPathOk allows the area to lie under the tracked path (area = p/…). That is not unsound, but it makes the closed theorem vacuous: Create's mkdir fails, or Open fails with ¬dbOpenOk.

**Evidence:** freeze-r3-3.md:182-185, 200-203; GooseLang/Ext/AbsDisk/Impl.lean:59-63, 264-265 (DirDurable ¬underDir); examples/etcd/mvcccrash/mvcccrash.go:231-237, 244; Paths.lean underDir.

**Fix:** Name the rung-3 area in §2.4, check it against D2's path and against DirDurable for the three TouchDirAll directories, and add `¬ underDir p area` (plus `s.dirs !! p = none`) to boltPathOk/absDiskInitOk.

### m3 (MINOR)

Composing with W4c's Q1 needs keep views. The crash obligation runs at ⊤ and must close the old generation's invariant with its contents unchanged. The package names only `boltFileAt_crash`, which consumes the old resource. Also, `absDiskCrashWal` is a single `∃ s s', crash s s'` package holding the old WAL half, so a tester holding both arms (rung 4) could not use a WAL keep lemma and a bolt keep lemma in the same crash proof unless the crash start is split per arm. Since crash is a per-field conjunction, the split is easy. The package should also say that durable's reservation, on which the hidden-name argument depends, carries into every generation under Q1's fresh names ('same reservation mode').

**Evidence:** freeze-r3-3.md:411-419; GooseLang/Ext/AbsDisk/Specs.lean:468-480 (absDiskCrashWal/CrashStart); /shared/tmp/wal-spec/w4c/plan.md:50-60, 212-216, 402 (Q1 and the keep variants).

**Fix:** Specify in §4: `absDiskCrashStart = absDiskCrashWal ∗ absDiskCrashBolt ∗ token`, with `boltFileAt_crash_keep` returning the old generation's `boltFileAt` alongside the new one, and cite Q1's carrying of `durableReserved`.

### m4 (MINOR)

The pins and evidence do not match the final code. The header and the line citations are to bbolt ea4cab5 (B/), but D7 moved the pin to 4f08974e (commit 438217f8c0), which changed Open: init re-runs on a torn file. §5.1's matrix ran at ea4cab5, where the init finding still occurs. The §5.2 binaries mvcccrash-*-mpci*.test (built 20:06-20:08) predate commit bdecad79b8 (20:11:56). The tester still uses `snap/db`, while D2's `.db` move lands only in R3-4.

**Evidence:** freeze-r3-3.md:7-9, 37-42, 443-458, 493-500; ls -l /shared/tmp/crash-rung3/mvcccrash-*mpci*.test; git show bdecad79b8; examples/etcd/mvcccrash/mvcccrash.go:225, 244.

**Fix:** Re-cite Open at 4f08974e (including the D7 branch, in boltOpened's docstring), state the source commit each §5.2 binary was built from, and rerun one control batch after the `.db` rename.

### m5 (MINOR)

Text and ripple loose ends: (a) absDiskExt's name is the WAL package path and its docstring says it is moved by the WAL's functions; it will now also hold bbolt's durability, so update the docstrings (Impl.lean:5-12, :178-180, which say `bolt : GMap GoString BoltDur` where the package uses BoltFile). (b) `Pos.Countable AbsDiskState` (Specs.lean:94) needs `Pos.Countable BoltFile`, not only BoltData. (c) The trust base grows (dbUntracked, dbTracked and their Persistent/Timeless instances, three new spec axioms), so etc/tcb-baseline.txt, the collections and the bbolt/backend interfaces change; list them. (d) The tracked axioms are stated over `boltFileAt`, so its definition (a half ghost variable plus an exclusive token, agreeing with absDiskCtx) is part of what they mean; freeze those three lines rather than leaving them to R3-4. (e) Name the GooseLang primitive syncDir's model uses for `nondet`.

**Evidence:** GooseLang/Ext/AbsDisk/Impl.lean:5-12, 178-188, 199-203; Specs.lean:94-97; freeze-r3-3.md:211, 256-271.

**Fix:** Add a short 'ripple' list to §3/§4 covering (a)-(e).

### m6 (MINOR)

No unneeded premise: `o.noGrowSync = false` looks unnecessary under the approved fsync(2) contract. fdatasync makes the size needed to read the data durable, and the old meta's pages lie within the old size, so a grow without its own fsync only loses unsynced tail bytes. The premise is harmless, since etcd sets both options from UnsafeNoFsync, but it costs an OptsM field and an axiom split (M2). Separately, the package says Open's one-commit branch (`!NoFreelistSync && !hasSyncedFreelist`) is 'not etcd's case'. Open_kv_trk cannot exclude that case (OptsM has no noFreelistSync), so the package needs the argument instead: that commit leaves the data unchanged and syncs itself, so it stays within boltCrash.

**Evidence:** freeze-r3-3.md:46-51, 292-293, 330 (note c); Spec/go_etcd_io/bbolt/Options.lean:47-48 (noFreelistSync dropped).

**Fix:** Either justify noGrowSync with the Go code (a filesystem where fdatasync does not cover the size) or drop it, and add the one-commit-branch argument to §1.

### m7 (MINOR)

Outside my lens, but the package should carry it: the user's decision of 2026-11-12 asks for the boltDisk axioms to be compared against the LinuxFs per-byte model (examples/osfs/bboltfs, notes/bbolt-port-plan.md, notes/walfs-ext-plan.md) when this package goes to review, and for convergence to be decided then. The package has no such section. The handoff defers it to a reviewer's lens.

**Evidence:** scope.md:562-563 (2026-11-12 user decision); notes/wal-crash-handoff/rung3-handoff.md:110; grep finds no 'LinuxFs'/'bboltfs' in freeze-r3-3.md.

**Fix:** Add a §8: where boltImg/boltCrash agree with or are weaker than bboltfs's bootCrashSafety and P1 relation, what convergence would cost, and a recommendation for the user.

> Verifier: refuted=False. The finding holds. Every piece of evidence checks out against the code. OptsM (BboltOptsDefs.lean:33-37) has only readOnly, pageSize, openFile and logger, and optsZero is a 4-tuple. optsAt_bool (BboltOptions.lean:89-96) is a trust-boundary axiom that lists NoSync and NoGrowSync among the fields whose store "keeps o". newBackend.lean:125-128 uses exactly that axiom for the NoSync and NoGrowSync stores. As things stand, then, nothing can establish Open_kv_trk's premise `o.noSync = false ∧ o.noGrowSync = false` (freeze-r3-3.md:292-293). Adding the fields requires restating optsAt_bool, which mean

> Verifier: refuted=True. The MAJOR claim does not hold. (U) adds two trust-boundary axioms per function, selected by a persistent witness: `dbUntracked db`, or `dbTracked db path` (freeze-r3-3.md:252-265 and 274-345). Logically this is the same as the proposed gated single axiom with `dbMode db m`, and the finding itself concedes "the same trusted content". Nothing in it forces the backend proofs to split. InvBackend can carry the persistent disjunction `dbUntracked db ∨ dbTracked db path ∗ …`, and one `batchTx.commit` proof can then case on it, calling `Commit_kv` or `Commit_kv_trk`. That is exactly the case split th

> Verifier: refuted=False. The finding holds against the worktree and the package. I could not refute it.

1. `goose_adequacy_start_files` (/shared/etcd-grove-rung3/Proof/runtime/Start.lean:183-213) is generic over `[GooseExts]`/`[GooseInterp]`. Its WP premise hands over both `extsLocalStart σ.world` and `[∗list] f ∈ Fs, backend.fileHolds f ∅`. With `absDiskExt` in the extension list, `localStart := absDiskStart` (GooseLang/Ext/AbsDisk/Specs.lean:455). After rung 3, per freeze §R3-4 at :414-416, that also hands `boltOwn s0.bolt`, which gives `boltFileAt f absent`. So one closed WP proof can hold `fileHolds f ∅` and the 
