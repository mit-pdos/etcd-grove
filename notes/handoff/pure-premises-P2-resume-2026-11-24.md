# P2 resume (kvN range)
Worktree /home/ubuntu/.claude-F/jobs/03d8018a/tmp/p2-kvN, branch premise-kvN-range/2026-11-24 (off origin/premise-witness/2026-11-24).
- [x] Go diffs applied
- [x] retranslated kv, kvreconf, kvdurable, kvdurable-noax (`--perennial ../perennial-b3f2`); copy-part.py rerun (--check ok)
- [x] Lean edits: MainN spec/proof (wp_if_destruct x2 early return), Adequacy/AdequacyLinked/Results/TopLevelRobustness/Witness for kv, kvreconf, kvdurable; RaftNoAx via copy-part + own witness
- [x] STATUS entry added, oldest moved to status-history
- [ ] VM build (log ../p2-b1.log). vmlake sync race: gc deletes a never-used sync dir mid-sync; worked around by holding .vmlake/inuse flock on VM during `vmlake sync`
- [ ] Go NV tests: kv, kvreconf ok; kvdurable rerun with -timeout 40m (../p2-gotest-kvdurable.log) — first run hit go test's 10m default; noax in p2-kvN/p2-gotest.log
- [x] VM build of the 13 leaf targets (kv, kvreconf, kvdurable, RaftNoAx kvdurablenoax): 5944 jobs, success, first try
- kvdurable TestMainNRange -v -timeout 40m: MainN(0),(1001) returned, MainN(1),(2) passed porcupine, then timed out in MainN(3) at 40m (machine under heavy disk load; goroutines in raft/kv loops, not deadlocked-looking). Log ../p2-gotest-kvdurable.log
- [ ] KvNet leaf build (../p2-b2.log), noax test (../p2-gotest-noax.log)
- [x] KvNet kvnet.TopLevelRobustness VM build: 4250 jobs, success
- noax TestMainNRange: MainN(0),(1001) returned; timed out (40m) inside the first in-range MainN (check.go:213, Run) under heavy IO pressure
- [x] committed c87e85ec2b, pushed to premise-kvN-range/2026-11-24. DONE except: full NV runs of kvdurable/kvdurablenoax on a less loaded machine
