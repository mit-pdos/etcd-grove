# C-I2: `bootstrapCrashContract.law` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/CrashInterim.lean`)

Review 2026-11-24, `axiom` skill, a fresh agent given the axiom and the fork (`upamanyus/etcd`
`768ecf158`, the torn-`Save` fix; its tests pass under go1.27.3). **Refuted as first stated**, two holes:

- **A1**: quantified over every `γ`, `dir`, `id`, while `bootOkR` asserts `γ.vs = ps ∧ ps ≠ []` and
  `memberDirIs dir`: at `γ.vs := []` the axiom proves `bootstrap` never succeeds (a program panicking on
  success is "proved" safe). The graceful contract is guarded at its use (`bootPremiseR`). Fixed: the law
  takes the deployment's names (`γ.vs = ps`, `ps` non-empty, distinct, no `0`, `id ∈ ps`,
  `srvBootLogOk ps γ.boot`, `dir` the bootstrap log's peer URLs).
- **A2**: without `i ≤ σ.commit`, an unsaved WAL (no state record) beside a backend that applied the boot
  entries meets the premises; the fork's `DiscardUnsaved` then takes the first-start branch, which `bootOkR`
  does not describe. Reachable (raft hands out the committed bootstrap batch before its `Save`; etcd applies
  before `Save`; the backend commits on its timer). Fixed: the contract asks `γ.cl.bootLen ≤ σ.commit`; that
  image goes to C-I3/T3 (uncovered yet).

Survived: the docstring's claim that the law is false at the pin `bc2b5f4d0` (confirmed); torn `Save`s,
commit-only `Save`s, a state record with an empty `HardState`, received snapshots and `.snap.db`
(`σ.b ≤ i`), a backend above the WAL's commit or last index (at the contract level), `cut`.

Caveat: `walFiles`/`walRead` match the fork's `ReadAll` only once layer 1 is re-proved over the fork's
`Save` (every `Save` with entries ends with a state record): the fix's phase P0-P3. Hence a law, not an
axiom, until then.

## Re-review (2026-11-24, a second fresh agent): **survives**
`ForceNewCluster = false` excludes the only consistent-index/commit comparison; `bootLen ≤ σ.commit` implies a
state record, so the WAL is kept; a torn state record is repaired and dropped, as `walRead`; `kvindex <
snapshot index` returns an error. Not checked in depth: a consistent index above the WAL's last index (harmless
under static membership); WALs written by older etcd (outside: every WAL is the fork's).
