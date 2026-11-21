# etcd_safe (examples/etcd/all): handoff

## START HERE (2026-11-21, E4 done: the subsumed closed theorems retired; STOP at the land stop)

- Plan: `/shared/tmp/coord-03/etcd-unified-plan.md` (D1-D6). Scope: `notes/etcd-unified-scope.md` (§4 the
  retirements). Decisions: `questions.md`.
- Branch `etcd-all`, worktree `/shared/etcd-grove-etcdall`, lean merged at 3ac6cb4031 (do not merge lean
  until the coordinator says). Not landed: the coordinator runs `etc/land.sh`.
- Environment: Perennial c8e356cb1, `--packages=/shared/tmp/manifest-c8e.json` (`.lake/package-overrides.json`
  a copy), `PERENNIAL_DIR=/shared/perennial-c8e356cb1`.
- E3 (`etcd_safe`, `etcd_robust`, collection `etcd-all.txt`): below, "E3".
- E4 (84aa52cdae): retired, with their `_adequate`/`_robust` forms, `etcd_{putget,putget3,putgetN,txnlin,watch,
  auth,auth3,lease,leasegrant,leaseexpiry,restart3,compacted,partition,partition_watch}_safe` and the composed
  drivers' own `etcd_{authN,authlease,leaseN,restartN,txnlinfaultsN,cache,compactwatch,leasecatchup,restart1}_safe`:
  their `Adequacy(Watch)`, `TopLevelDefs`, `TopLevelRobustness` (Proof, Spec), `PkgTable` (gen-init `PROGRAMS`),
  the closed parts of each `Results.lean` (the `*_Main` triples stay, over `MainLinked`/`Link`), 21 collections
  (72 -> 51). Moved unchanged: putgetN's `putgetNGF`/`heapAtN`/`putgetNGF_allG`/`putgetNGF_gooseGpreS` into
  leaseexpiryN (kept: `etcd_leaseexpiryN_safe`), `linkv3pAddrs`/`leasecatchupAddrs`/`leasecatchupDataDirs` into
  `etcd/all/TopLevelDefs`. Kept by the k8s precedent: every Go driver, its translation, `Init`/`InitLinked`,
  `MainLinked`/`Link`, triples (also of the drivers `etcd/all` does not run). No statement of a kept theorem
  changed; trust base 532 axioms, 0 sorry, unchanged (the triples keep every axiom reachable).
- Builds: full timed build 20261121-160659-1820494 OK; `etc/gates.sh`: `/shared/tmp/etcdall-e4/gates.log`.
- Left as is: Go comments naming the retired theorems (`examples/etcd/*/*.go`, `*_test.go`: a code change
  needs retranslation); dated plan notes (history).
- Next: land (coordinator), then the paper (below).
- Run Go as: `GOWORK=off PATH=/usr/local/go/bin:$HOME/go/bin:$PATH systemd-run --scope -q -p MemoryMax=32G
  go test -count=1 -run TestMainRun -v ./etcd/all` from `examples/`; never beside the drivers' own tests.

### E3

- `Proof/` and `Spec/.../examples/etcd/all/`: `holdToken`, `spawn`, the four part triples
  `KV`/`Auth`/`Lease`/`Restart` and `Main`, `MainLinked` (by hand), `Disjoint`, `Adequacy`
  (`etcd_adequate_of`), `Results` (`etcd_safe`), `TopLevelRobustness` (`etcd_robust : etcd_robust.spec`).
  Builds 20261121-154220-1696446, 20261121-155212-1759113; full 20261121-155243-1760503; gates passed
  (`/shared/tmp/etcdall-e3/gates.log`). Approved trusted docstring edit (`lease.leasesNoExpiry`): 69b194434a.

### Before E3 (E1, E2, F1-F5)

- E1: restartN at 14000/15000; new tokens txnlinfaultsN-12748, authN-133, authlease-1787, leaseN-1302,
  restartN-11208; drivers' `TestMemberIDs` at 300 (txnlinfaultsN 1000); `examples/etcd/all` (compacted in KV,
  leaseexpiryN out); builds 20261121-143444-1332646, 20261121-143848-1355091.
- E2: `TopLevelDefs.lean`, `etcd_robust.spec`. F1-F5: `MaxLeaseTTL` grants, header text, idutil docstring,
  guarded `Hprem…`; builds 20261121-152527-1552078, 20261121-152556-1553275. Go logs `/shared/tmp/etcdall-e1/`.
- The drivers' closed theorems still say `k ≤ 1000`; for authN/authlease/leaseN/restartN their ids premise
  is checked only to 300 now (docstrings say so). They retire in E4.

## After E4 (the user, 2026-11-21): update the paper
When the plan is done (E3 proved, E4 retired, landed), update the paper's Fig. 2 (grove-paper osdi27/theorem.tex,
`fig:theorems`): the etcd section's rows become `etcd_safe` (and `etcd_leaseexpiryN_safe` as its own row), with
counts from the paper's pipeline (Model/Driver/Verified/Axioms/Untr.), the caption's resource assumption (F4),
and the theorem.tex comment list of wanted theorems updated. Coordinator etcd-grove-03 does or delegates it.
