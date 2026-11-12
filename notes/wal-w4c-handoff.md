# WAL W4c: handoff

Branch `wal-w4c`, worktree `/shared/etcd-grove-walw3`, cut from lean `219ddbbb83` (W4b landed;
`wal-w4b` deleted). Coordinator: etcd-grove-81. Scratch: `/shared/tmp/wal-spec/w4c/`.

Goal (the user, 2026-11-11): the first rung of the crash ladder. Prove that the WAL robustness tester
(`examples/etcd/wal`) never panics under kill, power loss and kill-then-power-loss crashes, over
the crash-aware WAL spec (W4a, W4a.1, W4a.2, W4b). The closed theorems are `etcd_wal_adequate` and
`etcd_wal_safe`.

## State (2026-11-12)

- Plan `/shared/tmp/wal-spec/w4c/plan.md` approved by etcd-grove-81 (Q1, Q2, Q3, Q5) and the user (Q4,
  `walCreateOk` as a listed world-assumption premise; its docstring names Create's cleanup I/O,
  wal.go:294-309). Recorded in `questions.md` (untracked, gitignored).
- Q1 (`GooseLang/Ext/Durable`) is done and committed. Rung 3 merges ours; tell etcd-grove-81 before
  touching Durable again.
- Step 0 done in `c9840f1022`:
  - the tester is in `examples/etcd/wal` with T-1..T-9;
  - the driver beside it (`*_test.go`, `crashtest/`) sets `SegmentSizeBytes` (`segSizeFor`), and
    `walSaveOk` moved there;
  - goose project `etcd-wal` and `wal.toml` (`purgeRound` names-only); the translation builds
    (`GeneratedProof...examples.etcd.wal`).
- CP1 matrix: `/shared/tmp/wal-spec/w4c/runs/matrix.sh`, logs in `runs/cp1/*.log`, binary
  `/shared/tmp/wal-spec/w4c/wal.test` (built at the commit, before a doc-only edit and gofmt).
  - 9 runs: the W3b matrix seeds plus `l-*`, 10 incarnations x 40 ops.
  - Read each log's `violations N` line. **Any violation is a soundness finding: stop.**
- R1 (gen-init) finding: `etc/gen-init.py` needs an `IsPkgInit` instance module for the tester (a
  `Base.lean` as `examples/etcd/restart/Base.lean`, fact `True`) and one for `fileutil` (none exists:
  the "instance modules" W4a hit). With them, add the root
  `github_com.mit_pdos.etcd_grove.examples.etcd.wal` to `ROOTS` and run
  `etc/gen-init.py github_com.mit_pdos.etcd_grove.examples.etcd.wal go_etcd_io.etcd.client.pkg.v3.fileutil`.
  Tried, then reverted (it crashes on the missing instance: `gen`, `imods[0]`). Do this at step 2
  (Lean), with the other `Defs`.
- Not done in step 0: the count of restarts the bounds accept only through a purged prefix (needs
  instrumentation; optional); R4's `entRoC` probe (deferred to step 2).

- **CP1 result (2026-11-12): 9/9 runs PASS, 0 violations, 0 harness errors.**
  - Runs: kill, ordered, posix x2, kill-then-power posix and ordered (W3b seeds), and l-kill,
    l-posix, l-ordered (10 incarnations x 40 ops).
  - About 11,000 restarts checked.
  - CP1 reported to etcd-grove-81.

## Next, in order

1. (CP1 done.)
2. The purgeRound Freeze: **approved by etcd-grove-81 (axiom review READY WITH CHANGES; minors
   m1-m5 applied, text and evidence only: docstrings, `notes/decisions.md` "WAL W4c" with the C6
   gate, the review's resurrect tests in `purge_test.go`, run 4's classification of the failed
   restarts).** Done.
   - `Spec/.../examples/etcd/wal/purgeRound.lean` (the spec), `Proof/.../wal/purgeRound.lean` (the
     axiom), `Proof/.../wal/PurgeBody.lean` (the body, proved: `purgeRound_commit`, and `cut ≤ pur`
     in every reachable state, `absCutLePur_*`);
   - `examples/etcd/wal/purge_test.go` (five tests, PASS);
   - `etc/goose.py`: `etcd-wal`'s `lean_roots` gained `os=`, `io/fs=` (step 0's translation imported
     Perennial's `os`, which clashes with this repository's when imported with the WAL specs);
     retranslated;
   - Freeze package `/shared/tmp/wal-spec/w4c/freeze-purge.md`.
   - The purge-biased run (81's addition): `runs/purgebias.sh`, patch `runs/purgebias.patch` (not
     committed: applied, binary `/shared/tmp/wal-spec/w4c/purgebias.test` built, reverted), logs
     `runs/purgebias/*.log`; read `violations N` and `strict-rejected/relaxed-accepted N` (the count
     of restarts accepted only through a purged prefix). Runs 2-3 (`purgebias2/3`, targeted mode
     asked for by 81: 1 KiB segments, a round after every own snapshot, crashes right after a
     deleting round) add PURGESTATS/PURGEDIFF. Result (Freeze package §6): 0 violations in 21,969
     restarts; 12,725 restarts on purged directories; PURGEHITS 0 and PURGEDIFF 0: the purged arm
     never offers a read other than the full one (W4b's `walReadFrom_eq`), so the case is
     unreachable for the tester by construction.
   - Pitfall: pass `-scratch` as an absolute path (a relative one makes the driver see no WAL
     files).
   - After the review: apply its fixes; then step 2.
3. Step 2 (plan §8):
   - **Q1 done at `59a986cf94`** (go from etcd-grove-81; rung 3 told to stay out of Durable and merge
     ours). `GooseLang/Ext/Durable/Crash.lean`: fresh ghost names per generation (`durableCrashStart`:
     the old generation's ctx half and reservation authority, plus the new generation's half of the
     same files and the reservation element in the same mode), `durableOwnM_crash_keep`,
     `durableOwnM_crash`, `durableReserved_crash`. `GooseLang/Ext/AbsDisk/Specs.lean`:
     `absDisk_crash_view_keep`, `walDiskAt_crash_keep`, `walDiskAt_crash_any_keep`,
     `walAbsent_crash_keep` (interface `interface/GooseLang/Ext/AbsDisk/Specs.txt` regenerated;
     api-check clean). The targeted build of the 16 leaf importers of AbsDisk/Specs passes.
   - Next, in order:
     a. R1: the tester's package init. `Proof/.../examples/etcd/wal/Base.lean` (IsPkgInit, fact
        `True`, as `examples/etcd/restart/Base.lean`) fails on `raftpb`'s missing `IsPkgInit`
        instance: first find which instance modules its imports need (raftpb, wal, walpb, zap,
        fileutil, lib/durable), as restart's Base imports `etcdstart.Base`. Then add the root to
        `etc/gen-init.py`'s `ROOTS` and run it for the tester and `fileutil` (the handoff's R1 note
        above). If an instance needs a trust axiom, STOP (hard stop).
     b. `Proof/.../examples/etcd/wal/Defs.lean`: the tester's model (oracle ↔ WalHist), the
        invariant of plan §2.
     c. `RefLemmas.lean`: the transliteration of `ref.go` ↔ WalHist (`walImg_ext`, the image
        enumeration, the name bound).
     d. `Crash.lean`: `tester_crash`, using the keep lemmas (the crash obligation opens the old
        generation's invariant at `⊤` and closes it with its contents).
     Then CP2 (report).
   - **Done (2026-11-12, fresh agent step 2):**
     a. R1 at `efd2541007`: instance modules (facts `True`) `Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/Base.lean`,
        `Proof/go_etcd_io/etcd/server/v3/storage/wal/walpb/Base.lean` (imports raft's `Base` for raftpb/protoimpl),
        `Proof/.../examples/etcd/wal/Base.lean` (imports `wal.Init`, which the WAL specs import anyway); root added
        to `etc/gen-init.py`'s `ROOTS`; `Init.lean` generated for the three (fileutil's and walpb's carry the
        standard generated `opaqueInitsOk`/`initFuncsOk`, plan §4's "wal/fileutil/walpb initializer axioms";
        reached by no root yet). `gen-init --check` clean; `...examples.etcd.wal.Init` builds.
     b. `Defs.lean` at `f009626d5d`: `TOp`/`TContents`/`TCand`/`TOracle` (over the Go structs `hardState`,
        `entry`), `ref.go` transliterated (`tRead`, `tReadFrom`, `tReadCut`, `tImgs`, `tLastIdx`, `tCutPos`,
        `tNameBound`, `tOpenBound`, ...; `w64` where Go uses `uint64`), `tEncodeOracle`, `absOp`/`absC`/`projC`,
        `tHistWf`, `tCandOk`/`tPreOk`, `tRelI`, `TInvBody`/`TInv`/`TBoot` (plan §2.3).
     d. `Crash.lean` at `f009626d5d`: `tester_crash` proved (plan §2.4), over the keep lemmas plus new proved
        lemmas in `AbsDisk/Specs.lean`: `dirDurable_crash_keep`, `walArea_crash_keep`,
        `walDiskAt_crash_any_keep0` (Create's committed WAL has no `walSyncedLb` until Create returns),
        Timeless instances of `absPast`/`walArea`/`walSyncedLb`/`walNamed`/`dirDurable`.
     c. `RefLemmas.lean`: part A at `bde0b3afe5` (`tReadCut_abs`: the reads commute with `absOp`, no bound
        needed), part B at `e5b1d150ab` (`tImgs_complete`).
   - **Left of step 2 (next agent, in order):**
     c'. RefLemmas part C (part D, `tNameBound_le_openBound`, done): `tLastIdx_abs` (`uint.nat (tLastIdx h) = walLastIdx (h.map absOp)`), `tCutPos_abs`
        (`tCutPos h b = true ↔ walCutPos (h.map absOp) b`), `tNameBound_eq` (under `¬ walHasMaxIdx`, i.e. from
        `tHistWf`, and `h.length < 2^64`: `uint.nat (tNameBound h a) = walNameBound (h.map absOp) (uint.nat a)
        false`); readback (`fromRaft (absEnt e) = e` for `tEntWf e`) can wait for step 3 (it needs
        `fromRaft`'s Lean model).
     e. (done: AbsDisk interface regenerated at `0922c63aec`, api-check clean, the 18 leaf importers of
        AbsDisk/Specs build; tcb `--check` matches the baseline, 865 axioms / 5 sorries: the new Init axioms are reached by no root yet).
     Then CP2 (report).
4. **Step 3 (in progress, fresh agent 2026-11-12, after CP2's acceptance).**
   - CP2 accepted by etcd-grove-81 (recorded in `questions.md`): the fileutil/walpb Init axioms (+4),
     the new AbsDisk lemmas and Timeless instances, the invariant's shape.
   - RefLemmas part C done at `32607e360b` (`tLastIdx_abs`, `tCutPos_abs`, `tNameBound_eq` under
     `tHistWf h` and `h.length < 2^64`, plus `tHistWf_noMax`, `tLastIdx_lt`).
   - `Rep.lean`: the representation predicates (`opRep`, `opsElems`, `opsRep` read-only op slices,
     `candRep`/`candsElems`/`candsOwn`, `contentsRep`, `oracleRep`, `readRes`, `entsRes`), the
     `DecidableEq` instances of `THs`/`TEnt`, `ret_gen` (generalize `HΦ`'s value, then each branch
     proves its value equal), `opsElems_lookup`/`_snoc`/`_nil`/`_length`.
     Design: entry slices and op slices are read-only (`↦*□`) once built (copyOps shares the entry
     slices); appendable ones (`since`, `opens`, a function's own fresh slice) carry
     `ownSliceCap` and are appended with `wp_slice_append_persistent`; the candidate slice is owned
     (`m.o.cands[ci].unl = b` writes in place).
   - Specs and proofs done (Spec/ and Proof/ `…/examples/etcd/wal/<fn>.lean`, each proof taking
     its callees' specs): `hsEmpty`, `hsEq`, `entEq`, `phsNext`, `walMustSync`, `copyEnts`,
     `copyOps`, `walLastHS`, `readEnt` (premise: the entry's index `< 2^63`), `walSaveSnap`,
     `walFoldChk` (premise `tHistWf h`). All build with `lake build` (`b4a2cfc3bb`).
   - **Left of step 3, in order** (ref.go first, then oracle.go, then wal.go):
     - `walRead` (filter loop then `walFoldChk`; `tRead`), `walReadFrom` (`h[k:]`, the newest-pair
       loop `tNewest`, then the fold loop from `⟨tLastHS (h.take k), i, t, []⟩`; reuse the walFoldChk
       proof's inner/outer loop shape and `tFoldChkFrom_take_succ`/`_save`/`_snap`,
       `tReadEnts_take_succ`, `tReadEnts_prefix_none`, `tFoldChkFrom_prefix_none`), `walReadCut`;
     - `contentsEq`, `opEq`, `histEq` (return `decide (a = b)` over the records), `cutPos`,
       `lastIdx`, `nameBound`, `openBound` (`tNameBound`, `tOpenBound`), `walImgs` (`tImgs`; needs
       `opsRep` of `h[:j]`: a lemma from `ownSlice_slice`), `walFold`/`appendEnts` (no-panic, the
       result's entries among the history's: `opResend` saves them, so they must be well formed);
     - oracle.go: `putU64`, `decoder.u64`, `putHS`, `decoder.hs`, `putOps`, `decoder.ops`,
       `encodeOracle` (`tEncodeOracle`), `decodeOracle` (round trip on `tEncodeOracle o`),
       `freshOracle`, `loadOracle` (first `durable.Read`, mode `none → some area` via
       `durableModeStep`), `storeOracle` (opens `TInv`, updates `γo`; each call site gives the
       `tRelI` step);
     - wal.go: `newRnd`/`rnd.next`/`rnd.choose`, `entData`, `newU64`, `toRaft` (`entRoC`, R4),
       `fromRaft` (the read-back `fromRaft (absEnt e) = e` for `tEntWf e`), `toHS`, `restartRead`,
       `addCand`, `checkRestart` (§2.5), the member operations, `Boot`, `Main`;
     - then CP3 (report: the specs proved, trusted text (none beyond purgeRound), full build, tcb
       --check, api-check, gen-init --check).
   - **Step-3 tooling** (scratch, `/shared/tmp/wal-spec/w4c/step3/`): `gen.py spec|proof NAME
     IMPORTS... < body` writes a file with the package boilerplate (`spec` body: header text,
     `---`, declarations); `goal.sh NAME` prints the goal at the first `sorry` of the proof file;
     `chk.sh NAME...` checks proof files (both through `etc/lean-check.py`).
5. Step 4 as in plan §8.

## Pitfalls

- **Step 3, `etc/lean-check.py`:** after edits it can report a `(kernel) application type mismatch` on
  an auxiliary `wp_proof._proof_1_N` that a fresh elaboration does not have: an artifact of the
  incremental server. `etc/lean-check.py --stop` and check again, or `lake build` the module (the
  check of record).
- **Step 3, proof patterns:**
  - `iframe` does not frame intuitionistic hypotheses: give `↦*□` facts with `iexact`
    (`isplitl []` first).
  - A persistent conjunct of a loop invariant comes back spatial after `wp_for`; make it
    intuitionistic at once (`icases H with #H`), or a later `wp_apply`'s precondition swallows it.
  - A load of a field of a slice element: `icases ownSlice_elem_acc … $$ Hs with ⟨Hv, -⟩`, then
    `iStructNamed Hv`, then `wp_auto`.
  - After `wp_for` of a loop whose body has `continue` or `return`, `cleanup_bool_decide` before
    `wp_if_destruct` (else the guard stays `#(decide …) = #true`).
  - A function that ends right after `make`/`append`: `wp_apply +noauto …`, then `ipersist`, then
    `wp_auto` (an `ipersist` needs a WP goal). Better: persist the fresh slice at once and append
    with `wp_slice_append_persistent`.
  - A record literal inside `iprop(…)`: write `contents.mk …` (`{ hs' := … }` does not parse there).
  - The Go struct `entry` clashes with a global `entry`: write `TEnt`.
  - A `return` inside a nested loop: `wp_for_post` once per loop, then `iapply HΦ`.

- **The crash obligation runs at `⊤` and cannot refute `crashed`.** So the old generation's invariant
  must be closed with its contents kept (crashlog's `cfInv_crash_keep`). This is why the durable
  extension's identity crash interpretation does not work for an invariant that also holds the WAL
  (plan §0.4).
- The landed `"WalPurge"` takes `k` by value: no `TrustedCode` model can perform it (plan §0.5).
- Since W4a revision 3, `Open` raises `unl` (persisting across crashes, clamped), so the tester's old
  `released`-based check is stronger than the spec (plan §0.3).
- The tester's oracle stores must precede the calls they cover: the `unl` bound before
  `ReleaseLockTo`, `pur` before `purgeRound`, `opens` before each `Open`.
- GOWORK=off only for our own Go test runs; never in the shell of `etc/goose.py`/`gates.sh`/`land.sh`.
- `notes/status-history.md` is append-only.

## Build command

```
export TMPDIR=/shared/tmp
systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build <module>
# full: flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build
```
