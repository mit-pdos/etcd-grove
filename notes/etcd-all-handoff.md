# etcd_safe (examples/etcd/all): handoff

## START HERE (2026-11-21, E3 done: etcd_safe and etcd_robust proved; STOP: report, E4 next)

- Plan: `/shared/tmp/coord-03/etcd-unified-plan.md` (D1-D6). Scope: `notes/etcd-unified-scope.md` (§8: E1/E2,
  the token table, `etcd_safe`). Decisions N1-N7, F1-F5, the statement: `questions.md` (user, 2026-11-21).
- Branch `etcd-all`, worktree `/shared/etcd-grove-etcdall`, lean merged at 3ac6cb4031 (do not merge lean
  until the coordinator says: lean moves to Perennial 04b42a139). Not landed.
- Environment: Perennial c8e356cb1, `--packages=/shared/tmp/manifest-c8e.json` (`.lake/package-overrides.json`
  a copy), `PERENNIAL_DIR=/shared/perennial-c8e356cb1`.
- E1, E2, F1-F5: below and scope §8. The approved trusted docstring edit (`lease.leasesNoExpiry` names
  authlease and leasecatchup at `MaxLeaseTTL`): 69b194434a.
- E3 (committed; `Proof/` and `Spec/.../examples/etcd/all/`): `holdToken`, `spawn` (the join idiom's
  `ownDone`, a token for `f`), the four part triples `KV`/`Auth`/`Lease`/`Restart` and `Main` (each the
  drivers' or parts' triples side by side; `wg.Add(n)` by `mvccrand.wp_Add_many`), `MainLinked` (by hand,
  as k8s/all's: no gen-link mode), `Disjoint` (generic `nodup_groups`: port intervals for addresses,
  prefixes for directories; `etcdStarts`, `etcdBridges`, perms, `hmsL`), `Adequacy` (`etcd_adequate_of`,
  `Main`'s triple a hypothesis, so it does not import the drivers' cones), `Results` (`etcd_safe`, the
  §8.2 text, `#print axioms`: no `sorryAx`), `TopLevelRobustness` (`etcd_robust : etcd_robust.spec`). No
  statement, axiom, sorry or trusted text changed beyond the docstring. Collection
  `etc/tcb-collections/etcd-all.txt`.
- Builds: 20261121-154220-1696446 (MainLinked, peak 2.6 GiB), 20261121-155212-1759113 (Results,
  TopLevelRobustness, peak 2.6 GiB); full timed build 20261121-155243-1760503 OK; `etc/gates.sh` all passed
  (log `/shared/tmp/etcdall-e3/gates.log`; trust base 532 axioms, 0 sorry, unchanged; 72 collections match).
- Next: E4 (retire the subsumed theorems, scope §4), a separate stage; then the paper (below).
- Run Go as: `GOWORK=off PATH=/usr/local/go/bin:$HOME/go/bin:$PATH systemd-run --scope -q -p MemoryMax=32G
  go test -count=1 -run TestMainRun -v ./etcd/all` from `examples/`; never beside the drivers' own tests.

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
