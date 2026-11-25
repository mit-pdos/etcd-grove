# P6 leaseexpiryN range: resume
Branch premise-leaseexpiryN-range/2026-11-24 @ 74e04c603b (pushed), worktree /home/ubuntu/.claude-F/jobs/03d8018a/tmp/p6-leaseexpiryN (off origin/premise-witness/2026-11-24).
DONE. Go diff + TestMainRange; retranslated; statement k : w64 without hk1/hk; `cluster k` (Defs.lean) drives addrs/dirs/startAddrs; Main.spec over startOf (cluster k).
VM build of leaseexpiryN TopLevelRobustness + Results: success (b5, no warnings in Main). Axioms of etcd_leaseexpiryN_safe_single_process = etc/tcb-collections/leaseexpiryN-single-process.txt.
Gates: premise-witness ok, tier ok, api ok, goose --check leaseexpiryN ok, bounds ok, gen-init --check ok.
Left: review of the k : Nat -> k : w64 statement change; witness still pending-b (BootFacts).
## Landing prep (2026-11-24, ~23:50Z, handoff pickup)
Merged origin/lean 2f8ee1548e, then 73d38b3f05 (Net/notes only; incremental rebuild exit 0) (statement keeps lean's new [os.file/os.fileStat.FieldAssumptions] binders; the approved k : w64 / no-range change unchanged). Generated files regenerated at Perennial fce59af75 (goose leaseexpiryN, gen-init, gen-specs-pkginit, gen-link, copy-part: no changes). premise-witness baseline: craq/gryff (new on lean) added as pending. VM build of TopLevelRobustness, Results, PremiseSat, FsStart and all 24 TopLevelWitness: exit 0 (12480 jobs), no sorry. #print axioms of the three results: 218 + 3 std = etc/tcb-collections/leaseexpiryN-single-process.txt. NV TestMainRange passes. Sent for the land queue.
