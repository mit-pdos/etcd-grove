# leaseN handoff

## START HERE (2026-11-16, second agent)

- Branch `leaseN`, worktree `/shared/etcd-grove-leaseN`. Not landed, not pushed. Statements (plan §2) APPROVED
  (1f781da0d6); D1-D12 decided (questions.md).
- Done: plan, Go and tests (first run); translation, Base, Init/PkgTable (1f781da0d6); Lean drafts of both programs
  (7260497c12, `etcdstart.kv_lease_served_go` added); drafts fixed until the proofs check (this run, see the log
  below and the next commit).
- Build: `/shared/tmp/build-slot.sh lake --packages=/shared/tmp/manifest-e9e.json build
  Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Results Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Results`
  (logs `/shared/tmp/leaseN/build*.log`). `etc/lean-check.py --max-open 2 --fast` for single files (`LAKE_OPTS=--packages=...`),
  `--stop` before a build and at the end of a turn.
- Done this run too: full build clean; trust base unchanged (877, 4); collections `leaseN.txt` (648 = leasekv ∪ putgetN)
  and `leaseexpiryN.txt` (649 = leaseexpiry ∪ putgetN), no sorry; etcdstart interface regenerated (`kv_lease_served_go`);
  STATUS entry (oldest moved to status-history).
- OPEN (etcd-grove-02): bounds +11 (leaseN 6, leaseexpiryN 5; putgetN/authN pattern), gates fail on it until decided
  (then edit `etc/bounds-baseline.txt`); the collection baselines are new trust-base text to review.
- Next: gates under `flock /shared/tmp/etcd-grove-full-build.lock` (LAKE_PACKAGES=/shared/tmp/manifest-e9e.json,
  PERENNIAL_CHECKOUT=/shared/perennial-e9e6351d9, GOWORK unset); STOP before `etc/land.sh`.
- Then (D10): `leasecatchupN`, a stage of its own.

**Pitfalls**
- Range loops (`for j := range ms`) still load `ms[j]`: the invariant tracks the hidden counter `i_ptr` and `j_ptr`, and the
  body first does `wp_load_slice_index msl`.
- `simp only [...] at *` also rewrites the `have`s (it turned `hnz` into `True`): rewrite the goal or one hypothesis.
- Do not port the one-member leaseexpiry check (TTL then listing): false through a follower (`TestTTLThroughFollowerPanics`).
- auth-lease S4 (`/shared/etcd-grove-rs56`) changes the client lease specs: do not edit those modules (plan D12).
- Go tests: `GOWORK=off PATH=/usr/local/go/bin:$HOME/go/bin:$PATH`, under `systemd-run --scope -q -p MemoryMax=32G`;
  `/shared/tmp/leaseN/runs.sh` reruns the matrix.

## History

- 2026-11-16 (first agent): plan, Go programs and tests (`/shared/tmp/leaseN/runs.log`, all pass at k in {1,2,3,5,7,9,15}),
  statements approved; translation; Lean drafts (unchecked). Died mid-run (tmux killed).
