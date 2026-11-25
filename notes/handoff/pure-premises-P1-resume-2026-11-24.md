# P1 (tracecheck bootstrap size) resume
Worktree /home/ubuntu/.claude-F/jobs/03d8018a/tmp/p1-tracecheck, branch premise-tracecheck-nodes/2026-11-24
(off origin/premise-witness/2026-11-24 f1c3f2b4a1, merged origin/tracecheck-nonvacuous 8002a9eab4 -> 5eb5285e44).
Status: setup done; starting step 1 (concrete ccDecodeV1).
- 2868511af2 step 1 (concrete ccDecodeV1, vectors) and 6dcef87544 step 2 (bootLog, boot/Hbf dropped, witness) committed in p1-tracecheck (unpushed until built); full VM build running (log ../p1-full1.log).
- Step 3 in worktree ../p1-tracecheck-s3 (branch p1-tracecheck-s3-local off 6dcef87544): Go diffs applied; NV test passed (sizes 1..5 x 10 seeds). Layer B (TraceSim/MainSim) is generic in the voter list C: CheckTrace's acceptance does not assume 3 servers; the 3 is only in the harness (ProbeA tcVoters, RunConcurrent, HarnessDefs, Fits +3, Cluster__handleReady tcMem).
- 09:00Z: full VM build of steps 1-2 passed except Defs (norm_num, fixed: step 2 now 9beaaee0da); incremental rebuild queued (../p1-full2.log). Step 3 committed as wip 04d57695a4-ish in ../p1-tracecheck-s3 (rebased on 9beaaee0da), STATUS entry included; its build queued (../p1-s3b1.log).
- 10:00Z: steps 1-2 pushed (9beaaee0da), full VM build exit 0. Step 3 tracecheck targets build exit 0 (no sorry); final full build running (../p1-s3full.log); then squash s3 wip commits, push to the branch.

## 2026-11-24 ~23:30Z: Upamanyu's review (#8 7145350752, "never lower the step bound"): stopped, needs a raft-core change
Asked: charge a receipt per bootstrap entry in `Main` (proof only), fit `receiptBound ≤ 2^61`, statement bound `2^61`.
This can't be done in `Main` or the harness alone. No Go or Lean change made; branch head = 285c4859a2 + this note.
- The `+ bootLen` comes from raft's protocol ghost: a leader's entry record carries `⧖ (index - γ.reBoot.length)`
  (`isEntryC`, `Proof/go_etcd_io/raft/v3/Protocol/Ghost.lean:1586`), and a boot entry is a `BootRec` with no
  receipt (`isEntryR_receipt` gives `⧖ 0`). So indices are `< receiptBound + bootLen` (`lastRec_receipt`,
  `readyFits`, `readyRest`'s `Lx`, ~100 `receiptBound GF + γ.reBoot.length ≤ traceNumBound` premises in
  ~50 files of `Proof/go_etcd_io/raft/v3`, copied to RaftNoAx/KvNet/RaftTla). Receipts that `Main` takes have
  nowhere to go: `cluster_alloc` takes none.
- A second `+ 2` does not depend on the boot log: the term budget `budgetInv` (`InvNodeChan.lean`) has
  `M ≤ k + 1` (bootstrap term 1 free), and the checker needs `t + 1 < 2^61` (`tc_bound`, `RunTracedOk`'s
  `receiptBound + 2 ≤ traceNumBound`, `startTrace`'s `receiptBound + max bootLen 2 ≤ 2^61`). Charging only
  the boot entries reaches `2^61 - 2`, not `2^61`.
- What it would take: a raft field for the uncharged prefix (`reFree`: `reBoot.length` for every existing
  client, so their statements stay as they are; `0` for the trace check). `isEntryC`/`BootRec` carry `⧖ index`
  for charged boot entries. `budgetInv` holds a deposit of 2 receipts. `cluster_alloc`/`budget_alloc_boot`
  take `⧖ bootLen ∗ ⧗ 2`. `Main`'s boot loop then threads `⧖ m → ⧖ (m+1)` per entry
  (`wp_GoInstruction_receipt'`). This changes raft-core's API and rebuilds every raft result. Waiting on Upamanyu.

## Landing prep (2026-11-25, handoff pickup; Upamanyu's decision: option (3), #8 7147073597)
Merged origin/lean e1ab967ea2 (premise-witness baseline: lean's kvudp lines kept, tracecheck's pending line dropped since P1 witnesses it). Generated files at Perennial fce59af75: goose tracecheck/raft-tla, gen-init, gen-specs-pkginit, gen-link, gen-raft-tla, copy-part consistent. Full VM lake build: 28441 jobs, exit 0. tcb-report --check: matches etc/tcb-baseline.txt (329 axioms, 0 sorries), identical to lean's baseline (ccDecodeV1 made concrete adds or removes no axiom). #print axioms raft_tracecheck_robust: 10 + 3 std = etc/tcb-collections/tracecheck.txt; raft_tracecheck_robust.premisesSat: std only. premise-witness --check, tier, import-all, bounds, api: ok. No Go change in the tracecheck module or its deps from the merge: TestMainRandomNodes not rerun.
Then merged lean 2fa4c36fd7 (premise-witness-fs: lean's baseline dropped the kvnet/kvudp lines, P1 drops tracecheck's): full VM build 28446 jobs, exit 0; tcb-report --check matches the baseline (329, 0 sorries), identical to lean's; raft_tracecheck_robust 10 + 3 std = tracecheck collection; premisesSat std only; premise-witness --check ok (44 statements, 32 witnessed).
