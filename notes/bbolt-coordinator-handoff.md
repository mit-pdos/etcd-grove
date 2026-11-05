# bbolt proof: coordinator hand-off (2026-11-05)

For the next agent that coordinates or finishes the bbolt proof. The detailed plan of record is
`notes/bbolt-proof-plan.md`, with its per-maintainer hand-off sections and the open-sorry
inventory. Spec decisions are in `notes/bbolt-spec-decisions.md`. This file says where things
stand, what is left, and how to work in this tree without breaking it.

## The ask (the user's directions)

- Verify bbolt (the fork `upamanyus/bbolt`, branch `goose-lean-v2`) in this repository. First design
  the specs with the `spec` skill and freeze them, then design the invariants, then prove them. Reuse
  `old/bbolt/` where it helps. The specs must be good for etcd, whose backend uses bbolt.
- The top-level goal is a concurrent bbolt test that another agent is adding to `lean`.
- Work method: the main agent coordinates, and subagents do the real work. Do the hardest pieces
  first. Decide spec questions yourself when the `spec` skill or precedent is clear. Ask the user
  only real judgment calls, and anything that changes trusted code or adds trust.
- If correct Go code is hard to prove, find the argument, for example by generalizing a Perennial
  spec. Do not refactor the fork for a non-bug (the page-pool case).
- Only real bugs justify fork changes, and those go to the user.
- Prove the frozen specs as they are; for example, writer reads stay fractional.

## Integration done (2026-11-05, after integrator-2; supersedes the state below where they differ)

- **Full `lake build` green** (13083 jobs). integrator-2's build failed only at `Write/CreateBktIfWp`,
  which its own last commit (`19386308ba`) had fixed.
- **Linked.** `etc/gen-link.py --bbolt` (`etc/link_bbolt.py`) writes `Link.lean`/`Results.lean`.
  Linking needed 18 duplicate declarations resolved: modules never imported together, each
  declaring the same name; the unused copy made `private`, or one copy renamed. A way to find
  such clashes without building `Link` repeatedly: read every module's `.olean` constant names
  (`Lean.readModuleData`) and compare; ignore stale `.olean`s whose source is gone.
- **Interfaces regenerated**, `--layout` baseline recorded (276 violations: lemmas and internal specs
  in proof modules; a clean-up item).
- **Trust.** `sort.SliceIsSorted`/`reflect.DeepEqual` are trust-boundary axioms now (approved);
  `links_pending` keeps `fs.FileMode.String.spec` (deferred to the lean merge) and
  `PidSetDeleteUnfold` (Perennial's fix landed at `542338360`; drop it at the pin catch-up).
- Left from the list below: the concurrent test, the backend switch, the merge, clean-up,
  Perennial proposals. `Open/ScratchInit.lean` is still untracked (owner unknown; not committed).

## State at ba28e7c8b8 (branch `worktree-bbolt-v2`, pushed)

- **Every frozen public triple is proved, and there are no `sorry`s** in `Proof/go_etcd_io/bbolt` or
  `Spec/go_etcd_io/bbolt`. The triples cover:
  - Open and Close;
  - Begin, Commit and Rollback;
  - Tx.Bucket, CreateBucket(IfNotExists) and DeleteBucket;
  - Bucket.Get, Put, Delete and Cursor;
  - Cursor.First, Last, Next, Seek and Prev (readers and writers, at any fraction; Prev is
    readers-only);
  - Info and Stats.
- **The proofs are not linked yet.** Each `wp_proof` takes its callees' specs as hypotheses, and
  there is no bbolt `Link.lean`.
- **The full `lake build` has not completed at this commit.** The last attempt was killed for low
  memory at about 11,000 of 11,991 jobs. `Commit/WriteExtRun` peaks at about 40 GB and takes about
  24 minutes. Build it alone first, then build the rest with low parallelism. Three files got a
  one-line fix that has not been checked: `Write/CreateBktIfWp`, `Write/DelWp`, `Write/DelBktWp`.
- **Perennial is pinned at `c6d352196`.** That is the old pin `b3e996d84` plus the pool change
  (`sync.Pool`'s `New` may assume a caller-lent resource, plus `isPool_respec`), and it lies on
  Perennial `lean`'s history. Catching up to Perennial `lean` (`3dd730372`+) means replaying etcd-grove
  `lean`'s three pin bumps (regenerated translations, about 130 proof steps). That catch-up belongs to
  the merge of this branch into etcd-grove `lean`, which is 387+ commits behind.
- **integrator-2 was launched with the remaining integration tasks.** Check `git log` for which of
  them landed:
  1. Finish the full build.
  2. Add `etc/gen-link.py --bbolt`, generate `Proof/go_etcd_io/bbolt/Link.lean`, and add
     `Results.lean` with `#print axioms`.
  3. Regenerate the interfaces: `etc/gen-interface.py etc/api/bbolt.txt`, plus `--check` and
     `--layout`.
  4. Run `etc/tcb-report.py --check`, review the diff, then `--check --update`. Add a bbolt
     collection `etc/tcb-collections/bbolt.txt`.
  5. Run `etc/verified-code.py` for bbolt.
  6. Update `notes/STATUS.md`.
  Redo whatever is not in `git log`.

## Trust and spec changes the user should review (all logged)

- **In `notes/bbolt-spec-decisions.md`:**
  - **D-H:** `receiptBound GF ≤ 2^62` is recorded in the database core; Open's spec already had it.
  - **D-I:** `fileHolds` requires a file size below 2^62.
  - **D-J/D-K:** writer-side invariants: the partial last page, and the highest page always written.
  - **D-L:** the freelist page's header names its own id.
  - **D-M:** `Tx.DeleteBucket` of the empty name may return `ErrIncompatibleValue`. Also filed as
    `nonissues/bbolt-deletebucket-empty-name.md`.
- **New trust:**
  - `Spec/strings/ToLower.lean` is a trust-boundary axiom (ToLower returns some string and never
    panics); the user approved it. Its Perennial follow-up is in `notes/perennial-changes.md`.
  - `fmt.Errorf`'s post was strengthened with `IsPointerError`; the user approved it earlier.
  - `etc/tcb-baseline.txt` must be updated for both (integration task 4).
- **Pending, needs the user's own sign-off:** Perennial branch `delete-map-named` (`6e6b05af3`). It
  changes Perennial's trusted map-delete semantics. Until it lands, bbolt uses the local
  `PidSetDeleteUnfold`. Once it lands: bump the pin and replace that lemma with
  `wp_mapDelete_underlying`.

## What is left after integration

1. **Check integrator-2's results.** The full build is green, Link and Results build, the interfaces
   are regenerated and the TCB baseline updated. Ask the user before updating the baseline if any
   axiom appears that is not on the list above.
2. **The concurrent bbolt test** is the top-level goal. Find it on etcd-grove `lean`; the other agent
   adds it under `examples/`. Prove it against `Spec/go_etcd_io/bbolt/Api.lean`'s triples, with an
   adequacy theorem.
3. **The backend switch.** etcd's backend proofs still rest on the old bbolt `_kv` axioms. Derive
   those as corollaries of the new triples, then delete the axioms. The trust baseline then drops.
4. **Merge into etcd-grove `lean`.** This includes the Perennial catch-up above, and the `Code/`
   regeneration with `etc/goose.py` for the newer translator. Use the integration-train pattern (one
   integrator merges, builds and pushes).
5. **Clean-up candidates** (or use the `proof-cleanup` skill):
   - duplicate lemmas: `pk_uNode`, `wsMs_congr'`, `pt_bkt_iff`, `parOK_of_bktLocal` (vs
     `BktEnd.parOK_of_local`), `wr_bigSepM_keys`, and Read's `viewWF_child`/`viewWF_branchWF` copies;
   - local lemmas in the proof file `Cursor__next_w.lean`, which `--layout` may flag;
   - the untracked `Open/ScratchInit.lean`, whose owner is unknown;
   - helper scripts in `/tmp` and `.lake/pool*`.
6. **Perennial proposals** to make as independent changes (`notes/perennial-changes.md`):
   - a `strings.ToLower` spec;
   - `struct_wp_alloc_pos` moved into `Golang/Theory`;
   - `ownMap` fractional splitting.
7. **Branches and worktrees** (CLAUDE.md "Branches"): delete the local `bbolt-pool-new-later` (now
   merged), and this worktree once its branch is merged.

## How to work in this tree (lessons; the agents' protocol file was in the job's tmp dir)

- **Ownership.** One shared worktree, many agents. Only a maintainer edits shared statements
  (`Inv/*`, `Model/*`, internal `Spec/**`, the plan); units edit their own files and report defects
  precisely. A shared module must build at every moment: develop in a scratch module, then land in
  one build window.
- **Committing.** Commit with `git commit -m … -- <paths>`. For a new file, `git add <path> && git
  commit -- <path>`, and never leave files staged. When the working tree mixes several agents'
  edits, commit only your own hunks. Push `origin worktree-bbolt-v2`; never force-push.
- **The check of record is `lake build`.**
  - `etc/lean-check.py -a` and `lake env lean` gave false passes several times.
  - The `/tmp/u7n-*.sh` overlay scripts hid a parse error.
  - Use `lake env lean <f> | grep -i error` in the edit loop, and `lake build` before relying on a
    result.
- **Replacing a `sorry` changes the module's public `.olean`** (the proof no longer mentions
  `sorryAx`), so every importer rebuilds. Prove such a lemma in a side module and paste it in during a
  rebuild that has to happen anyway. Editing a proof that has no `sorry` does not rebuild importers.
- **Memory.** Never let two builds compile `Commit/WriteExtRun` at once: two copies ran the 94 GB
  machine out of memory. Build heavy modules alone, use `LEAN_NUM_THREADS ≤ 4`, and check `free -g`
  first.
- **Kernel deep recursion.** Never relate `{x with f := big}` to `x` by `rfl` or `simp`; use field
  lemmas such as `metaSummed_txid`, `pubC_*` or `WDb.reslot.proj_*`.
- **Review internal contracts against the frozen triples they serve, fractions included.** The
  writer-read fraction was lost in U0b's internal contracts, and a deferred question about it was
  never answered. Keep deferred design questions in a tracked list with an owner and an answer.
- **Read the definitions before taking a "spec vs rework" decision to the user.**
