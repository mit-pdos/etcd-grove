# sync-gh handoff (merge of GitHub's lean into local lean, 2026-11-10)

Worktree /shared/etcd-grove-sync, branch sync-gh-lean. Scratch /shared/tmp/sync-gh/.

Done:
- `7558a3ef02`: merge of gh/lean (ffb55d5620) into local lean (0c3adbf69e). Textual conflicts only
  in notes: status-history.md every line of both sides (+ the two 2026-11-09 mvccfull F1 entries moved
  out of STATUS's Last updated), STATUS's Last updated the ten newest (all 2026-11-10), decisions.md
  both entries.
- Semantic check: gh's diff mentions none of the names premise-fixes-4/raft-entsize changed
  (rnSetLoggerOk, commonPremises, statusErrOk, errStrOk, argOk, errLeaf, http specs, swMsgBound,
  hbSt, BootLog); local's diff mentions none of gh's (NewLessor, NewStore, lessorCfg, leaseOwn).

- Full build at the merge: clean, no fix needed (13846 jobs). Gates (stopped at the coordinator's
  word after these): build, links, tcb (843 axioms, 5 sorries = baseline), collections 54 match
  (mvccfull's included), goose, gen-init ok.

Next: etc/land.sh (the coordinator's go, 2026-11-11). Originally planned: full build (flock + MemoryMax=64G, --packages=/shared/tmp/manifest-ddc.json); fix
merge breakages; gen-link, gen-init --check, gen-interface; tcb --check (mvccfull collection
re-derived); etc/gates.sh; land.sh (only with the coordinator's go).
