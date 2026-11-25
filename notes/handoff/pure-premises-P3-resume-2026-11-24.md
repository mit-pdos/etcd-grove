# P3 resume (mvccrand/mvccfull MainAt)
Worktree /home/ubuntu/.claude-F/jobs/03d8018a/tmp/p3-mvcc, branch premise-mvcc-mainat/2026-11-24, head 61abfae2e0 (pushed). WIP, UNBUILT.
VM sync key a6daa8be706cb392 (first sync done with the inuse-flock workaround).
- [x] Go diffs applied; dirFits as a run counter, absent = `err != nil && errors.Is(err, os.ErrNotExist)`
- [x] retranslated (goose.py --perennial ../perennial-b3f2 --project mvccrand --project mvccfull); gen-init (PERENNIAL_DIR=../perennial-b3f2)
- [x] WIP eef3ef2346 reviewed (2nd helper): goose.py adds os=/io/fs= roots (as other fs projects), gen-link extra import, StartFiles gains proved `start_rootClaim`; LstatAnyS/RootClaim/FileNames have no axiom/sorry. Nothing trusted.
- [x] merged origin/premise-witness 66eac57c9f (clean, 61abfae2e0); after it: goose --project mvcc* 0 files changed; gen-init --check ok (274 up to date); gen-link --mvccrand/--mvccfull match Link.lean
- [x] source gates: premise-witness --check ok, tier-check ok, api-check all ok
- [x] NV mvccrand TestMainAt: PASS (../p3-nv-rand.log)
- [ ] NV mvccfull TestMainAt: first run hit go test's 10m default timeout inside Run (machine loaded, as P2); rerun -timeout 90m was stopped at wrap-up (../p3-nv-full.log). Next: rerun on a quieter machine.
- [ ] VM build b1 never started (waited for a slot the whole time, then stopped at wrap-up; ../p3-b1.log has no compile output). Next: `vmlake build` of Proof.…mvccfull.{TopLevelRobustness,TopLevelWitness,Results}, Proof.…mvccrand.{TopLevelRobustness,TopLevelWitness}, Proof.os.LstatAnyS (the importers.py leaves of StartFiles), fix errors.
- [ ] then: STATUS entry (none yet), commit, push
