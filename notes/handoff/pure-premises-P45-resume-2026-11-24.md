# P4/P5 resume (etcd/all, k8s/all params)
Worktree /home/ubuntu/.claude-F/jobs/03d8018a/tmp/p45-params, branch premise-etcd-params/2026-11-24.
- [x] P4+P5 Go diffs applied; goose cluster3, etcd-all, k8s-all (--check ok after merge, 15:3xZ)
- [x] merged origin/premise-witness/2026-11-24 (66eac57c9f) -> a63b9f8ff2, clean
- [x] P6-style: etcdProgAddrs/etcdProgDirs, k8sProgAddrs/k8sProgDirs (TopLevelDefs; empty out of count range) in statements; Adequacy in-range branch rewrites if_pos
- [x] mulBelow proofs restructured (case split before wp_start)
- [ ] VM build b4 (log tmp/p45-b4.log; synced BEFORE the edits above) -> fix ParamsOk "unknown tactic", MainChecked, Adequacy
- [ ] leaves also: etcd.{leasecatchup,partition,txnlinfaultsN}.Results, k8s.{compactor,etcd3}.Results
- [ ] STATUS (predecessor's entry exists, update), gates, commit, push
## State at wrap-up (2026-11-24, ~16:10Z)
- Head d30a709664 (pushed): merge of premise-witness 66eac57c9f + WIP, UNBUILT.
- Build b4 (tmp/p45-b4.log) never got a VM slot (4 busy); killed at wrap-up. Last real errors: tmp/p45-b3.log (pre-merge).
- Known/likely failures: etcd+k8s ParamsOk "unknown tactic" (b3: at `rotate_left` inside local macro params_next, and `decide` at 65:26 -- cause unknown, rotate_left exists in core v4.34.1; test on VM with `vmlake env lean`); MainChecked (both) unverified; Adequacy (both) in-range branch now rewrites `if_pos hc` on HAs/HDs/HWal (unbuilt); mulBelow (both) restructured, unbuilt.
- Next: vmlake -j 48 build the two TopLevelRobustness + cluster3.Link + Results leaves (etcd.{leasecatchup,partition,txnlinfaultsN}, k8s.{compactor,etcd3}); fix; STATUS entry (predecessor's exists, mention P6-style lists); gates; final commits.
## Landing prep (2026-11-25, handoff pickup)
Merged origin/lean up to c28e266cb4 (raft-retire landed: the four kv-family witnesses dropped; rebuilt, 12932 jobs, exit 0; axioms rechecked). Statements: only lean's new [os.file/os.fileStat.FieldAssumptions] binders added; the approved P4/P5 change is unchanged. Fixes for those binders: wp_MainChecked (MainLinked) and the MainChecked corollaries (Results) of etcd/all and k8s/all take them, as wp_Main does on lean. Generated files at Perennial fce59af75: goose cluster3/etcd-all/k8s-all, gen-init (PkgTables), gen-specs-pkginit, gen-link, copy-part: consistent. premise-witness baseline: craq/gryff (new on lean) added as pending. VM build of cluster3.Link, etcd/all and k8s/all TopLevelRobustness+Results, the etcd leasecatchup/partition/txnlinfaultsN and k8s compactor/etcd3 Results: exit 0 (12901 jobs), no sorry. #print axioms of every theorem of Results/MainLinked/TopLevelRobustness: etcd 252 + 3 std = etc/tcb-collections/etcd-all-single-process.txt, k8s 270 + 3 std = k8s-all-single-process.txt. NV TestParamsOk (etcd, k8s) pass. Sent for the land queue.
