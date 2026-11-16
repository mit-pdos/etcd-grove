# restartN handoff (branch `restartN`, worktree /shared/etcd-grove-restartN)

Plan: `notes/restartN-plan.md`. Statement draft (HARD STOP, with etcd-grove-81): `notes/restartN-draft.md`.
Decisions: `questions.md` (worktree-local, gitignored).

## Done
- S1 (`6e059747da`): `examples/etcd/restartN` (Go, `TestMemberIDs`, `TestFindToken`, `TestRun`), goose project `restartN`,
  translation. TestRun 20/20 (`/shared/tmp/restartN/runs20.txt`).
- S2 (`84da2991f3`): `Defs`, `Dir`, copies of restart3's `build`/`newMember`/`raftSwap`/`put`/`stop`/`check` specs and
  proofs over restartN's names (`stop` takes `k`); `restart/Swap.lean` and `restart/KV.lean` imported (`open etcd_restart`).
- S3 (`16b006c49c`..`e9159a1d85`): `startMembers` spec/proof, `Run` and `Main` specs and proofs. Targeted build green.

## Decided (etcd-grove-81, 2026-11-15)
Q2 (local startMembers with raftSwap), Q3 (N1 for the two candidates), Q4 (name `etcd_restartN_safe`) approved. Q1 (the
range of `k`) is with the user, with the statement.

## Prepared (independent of the range)
`etc/gen-init.py` (restartN in ROOTS and PROGRAMS; `PkgTable.lean`, `Init.lean` generated, `--check` clean),
`MainLinked.lean` (`etcd_restartN.wp_Main`); targeted build green (`/shared/tmp/restartN/build-link.log`).

## Next, in order
1. HARD STOP (current): wait for the range of `k` (Q1).
2. Link: `Adequacy.lean` (putgetN's `etcd_adequate_members` with
   `ms = startAddrs k`, `restartNAddrs_perm/_nodup/_lit`, `restartNDirs_perm/_nodup`; restart3's GF), `Results.lean`,
   collection `etc/tcb-collections/restartN.txt` (expect restart3's 530), interfaces, bounds (likely + a few
   `spec-thread` in `startMembers`/`Run`, as putgetN), STATUS entry, gates; then the hard stop before land.sh.
3. Optional cleanup: `Run.lean`'s unused simp args (579/580) and never-executed tactics (444/475).

## Pitfalls
- A wp_bind'ed `If` whose WP is proved under `wp_wand`: pass the pointers the condition reads (`srvs`, `k`) into the
  frame and return them in the post, or `wp_auto` makes no progress.
- `wp_if_destruct` on `i < N1` here gave `Hif : #(decide …) = #true`: `of_decide_eq_true (go.intoVal_inj Hif)`.
- `word` inside the loop bodies of `Run` failed with "unknown free variable": the counter lemmas `L1`/`L3` are stated
  right after `intro`.
- Lean-check: `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json etc/lean-check.py -q --fast -a FILE` under
  `systemd-run --scope -q -p MemoryMax=48G`.

## Build
`lake --packages=/shared/tmp/manifest-e9e.json build Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Main`
(64G cap). Go: `cd examples; GOWORK=off go test -c -o /shared/tmp/restartN/restartN.test ./etcd/restartN/`, then the
binary once per run (`-test.run TestRun`, `RESTARTN_MEMBERS=k`).
