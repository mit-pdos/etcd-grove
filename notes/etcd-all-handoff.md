# etcd_safe (examples/etcd/all): handoff

## START HERE (2026-11-21, E1, E2 and the review's F1-F5 done, STOP: statement review)

- Plan: `/shared/tmp/coord-03/etcd-unified-plan.md` (D1-D6). Scope: `notes/etcd-unified-scope.md` (§8: E1/E2,
  the token table, the planned `etcd_safe`). Decisions N1-N7: `questions.md` (user, 2026-11-21).
- Branch `etcd-all`, worktree `/shared/etcd-grove-etcdall`, lean merged at 3ac6cb4031. Not landed.
- Environment: Perennial c8e356cb1, `--packages=/shared/tmp/manifest-c8e.json` (`.lake/package-overrides.json`
  a copy), `PERENNIAL_DIR=/shared/perennial-c8e356cb1`; `.lake/build` seeded from authm3 at 3ac6cb4031.
- E1 (committed): restartN at 14000/15000; new tokens txnlinfaultsN-12748, authN-133, authlease-1787,
  leaseN-1302, restartN-11208 (leaseexpiryN unchanged: not in etcd_safe); drivers' `TestMemberIDs` at 300
  (`idMembers`; txnlinfaultsN 1000); `examples/etcd/all`: leaseexpiryN out, compacted in KV, counts `k1..k5`;
  goose project `etcd-all`, gen-init root (`all/Base.lean` by hand; Init/InitLinked/PkgTable generated).
  Builds 20261121-143444-1332646 (the five drivers' Results/TopLevelRobustness, all.InitLinked) and
  20261121-143848-1355091 (the new spec) OK. Go: TestAddrs, TestMemberIDs, TestMainRun k=3 (30 s) and -race
  (38 s) pass; logs `/shared/tmp/etcdall-e1/`.
- E2 (committed, lean-checked, built): `Proof/.../examples/etcd/all/TopLevelDefs.lean`,
  `Spec/.../examples/etcd/all/TopLevelRobustness.lean` (`etcd_robust.spec`); `etcd_safe` planned in scope §8.2.
- F1-F5 of the spec review (`/shared/tmp/etcdall-e2/review.md`, approved by the user; scope §8.3): authlease
  and leasecatchup grant with `MaxLeaseTTL` (Go, Lean `grantTTLv`/`grantTTL`, retranslated); the spec's
  header states the retired theorems' losses and the file semantics' I/O and fd assumptions; `Hprem…`
  guarded by `n + 12 ≤ 2 ^ 40`; idutil's trusted comment names etcd/all. Builds 20261121-152527-1552078
  (idutil), 20261121-152556-1553275 (authlease.Results, leasecatchup.TopLevelRobustness, all spec,
  all.InitLinked) OK, no proof changed. Go: authlease, leasecatchup packages; etcd/all TestAddrs,
  TestMemberIDs, TestMainRun k=3 (30 s) and -race (39 s) pass; logs `/shared/tmp/etcdall-e1/f*.log`.
- Waiting: the statement review of the revised spec (hard stop). Next after approval: E3a KV part (`spawn`, `holdToken`, `KV`
  triple), E3b-d, E3e (`Main`, `Disjoint`, `Adequacy` via `etcd_adequate_members_below`, `Results`,
  `TopLevelRobustness` proof, gen-link `--etcdall`), E4 retirements.
- The drivers' closed theorems still say `k ≤ 1000`; for authN/authlease/leaseN/restartN their ids premise
  is checked only to 300 now (docstrings say so). They retire in E4.
- Run Go as: `GOWORK=off PATH=/usr/local/go/bin:$HOME/go/bin:$PATH systemd-run --scope -q -p MemoryMax=32G
  go test -count=1 -run TestMainRun -v ./etcd/all` from `examples/`; never beside the drivers' own tests.
