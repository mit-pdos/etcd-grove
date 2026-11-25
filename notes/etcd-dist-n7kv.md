# N7-kv: the kv dispatch of `examples/etcd/dist/client` (M1, `etcd_kv_safe_nocrash`)

Task: issue #50, the lead's request of 2026-11-25T16:48:43Z; plan `notes/etcd-dist-plan.md` §11.3 (on
`etcd-safe-p9`). Prove `client.MainDeployment`/`Orchestrator`/`NodeDeployment`, kv arms only, the other arms
unreachable under M1's premise `KvOnly d` (every workload's kind is 0).

## Base of the branch (why not `lean`)

`etcd-safe-n7kv` is **`etcd-safe-bootax/2026-11-25` @ `c14f88dec2`**, not `lean`: `lean` (`08313db96d`) has no
translation of `dist/client` or `dist/kvremote` (they come with `etcd-safe-lit`, D2 `0048d170b5` and later), and
merging `lit` into `lean` conflicts in 26 files, the round-3 base `5a1c41d945` in 33. bootax is on the lead's
no-crash line and is the base `etcd-safe-p9` and `etcd-safe-n2/2026-11-25` share (`5a1c41d945`), so this branch
ports onto the landing line as they do. It carries the round-3 line's P7/P8 crash-spec merges (as do bootax, N2
and P9), but no T4/T7/P5/r4 work (only T4 round-4 *notes*). N2 was **not** merged (not needed: no N2 draft is a
callee here). Nothing was cherry-picked from P9: P9 has no `Orch`/`Node` spec yet, so they are schemas (below).

## The specs (written first; `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/`)

Vocabulary `Proof/.../dist/client/KvDefs.lean` (defs): `KvOnly d`, `rotateL`, `readySpec f` (a `func()` safe to
call), `orchShare OP d j` (`OP (d.nodes[j]) (d.workloads[j].ops)` when workload `j` exists), `nodeShare NP d n`
(`NP (W64 c) a (rotateL members' clients c)` at `d.nodeList[n] = (_, c, a)`), and the pure lemma `kvOnly_bounds`
(well-formed + `KvOnly`: ≤ 64 members, each `0 ≤ clients < 2^31`).

Callee schemas (P9's future specs are instances; step 6 proves `Orch.spec → Orch.specWith (its pre)`):
- `kvremote/OrchWith.lean`: `Orch.specWith OP`: `{pkgInit kvremote ∗ nodes ↦*□ ns ∗ OP ns ops} Orch(nodes, ops,
  tmo) {r. r ≠ "Illegal"}` for every `tmo`.
- `kvremote/NodeWith.lean`: `Node.specWith NP`: `{pkgInit kvremote ∗ eps ↦* epsL ∗ NP c addr epsL} Node(c, addr,
  eps) {True}`.

Dispatch (each parametric in `OP`/`NP`; post `True`, i.e. no panic):
- `deployment/Deployment__Endpoints.lean` (`deploymentRepr v d` → new `sl ↦* d.members.map client`),
  `deployment/Deployment__Node.lean` (`ok` → `n` names `d.nodeList`'s entry at `j`, `c`).
- `client/Rotate.lean` (generic; `0 ≤ i`, `i + len < 2^63`: Go's `(i+j)%k` would panic otherwise),
  `client/RunKV.lean`, `client/MainReady.lean` (`⌜w.kind = 0⌝`), `client/MainDeployment.lean`,
  `client/Orchestrator.lean` (`⌜KvOnly d ∧ Fips off⌝ ∗ deploymentRepr v d ∗ orchShare OP d j`),
  `client/NodeMain.lean` (`⌜w.kind = 0 ∧ clients + |eps| ≤ 2^63⌝`), `client/NodeDeployment.lean`.

## The proofs: state (2026-11-25, second session)

**All proved, no `sorry`, no axiom** (each compiled with plain `lake env lean` on fk-lean1):
`Deployment__{Endpoints,Node}`, `Rotate` (with `srem_of_nonneg`), `RunKV`, `MainReady`, `MainDeployment`,
`Orchestrator`, `NodeMain`, `NodeDeployment`, `KvDefs` (`kvOnly_bounds`, new `wellFormed_nodes_length`).
`deployment/Link.lean` regenerated (`etc/gen-link.py --deployment > .../Link.lean`: it writes to stdout), giving
`Deployment.wp_Endpoints`/`wp_Node`; `KvLinked` gives `wp_OrchestratorKv OP hOrch`, `wp_NodeDeploymentKv NP hNode`.
`etc/tier-check.py --check` ok; `etc/api-check.py` ok on every list (no new warning). fk-lean1 `lake build
KvLinked deployment.Link`: 4708 jobs, exit 0 (log `/shared/tmp/n7kv-build3.log`).

Proof notes:
- The pointer-receiver call `MethodResolve (PointerType Deployment.ty) "Endpoints"` on the local `d` goes
  through `wp_method_call; wp_call; wp_auto` to the value-receiver spec (`#(methods Deployment.ty …)`).
- `GoInterface` error checks: `cases err with | ok i => … | nil => …`, not `wp_if_destruct`.
- An `orchShare`/`nodeShare` in the Iris context is rewritten by a Lean `have hsh : … = …` and `rw [hsh]` on
  the goal (no `rw … at` an Iris hypothesis).
- `etc/lean-check.py` (incremental) reported spurious kernel errors (`wp_proof._proof_1_13` type mismatch) and
  missed errors after a `-a`; `lake env lean FILE` is the reliable check (`/shared/tmp/n7kv-lean.sh FILE`).

## Spec review (spec-reviewer, 2026-11-25, given only the Go code and the specs)

Verdict: every spec is sound and proved. Approve as is: `RunKV`, `Deployment.Endpoints`, `Node.specWith`. Approve
with nits: everything else. No reachable panic under the premises. Applied (below, "The review applied"):
- **F1** (recommended): gate `orchShare`/`nodeShare` and `KvOnly` by `WellFormed`, i.e. `⌜d.WellFormed⌝ -∗ …` and
  premise `(d.WellFormed → KvOnly d) ∧ Fips off`. The Go code reads them only after `WellFormed` returns nil, so
  this precondition is strictly weaker, and `BootBad.lean`'s `clientBadWp`/`nodeBadWp` could then use these specs
  instead of re-stepping the bodies. The proofs change by one `ispecialize` in the `nil` arm.
- **F2**: add laws `deploymentRepr_workloads`/`_nodes` (in `Repr.lean`) and `orchShare_eq`/`nodeShare_eq` (in
  `KvDefs`), instead of the client proofs unfolding `deploymentRepr`/`orchShare`/`nodeShare`.
- `NodeMain`: bound only `c` under its guard (`0 ≤ c → c < clients → c + |eps| < 2^63`), not `clients + |eps|`.
- `Rotate`: `i + len ≤ 2^63` (not `<`), and nothing needed when `xs = []`.
- `Deployment.Node`: also state the converse (`ok = true ↔ n` is in `nodeList`'s range), or name it as the margin.
- `Orch.specWith`: `∀ tmo` is stronger than `RunKV` needs (it passes `kvCheckTimeout`); keep it only if P9's
  `Orch` is timeout-agnostic.
- `MainReady`: for N7 (all kinds), `OP ns w.ops` should become the kv entry of a per-kind share.
- Go nits (candidates for `nonissues/`, not written): `Rotate`'s doc omits `0 ≤ i`/no overflow; for kv,
  `ready()` runs twice (`MainReady` and `RunKV`), against the doc's "called once".

## The review applied (2026-11-25, third session; the coordinator's decision)

- **F1**: `Orchestrator`/`MainDeployment`/`NodeDeployment` take `⌜(d.WellFormed → KvOnly d) ∧ Fips off⌝ ∗
  deploymentRepr v d ∗ (⌜d.WellFormed⌝ -∗ share)`; the proofs `ispecialize` the share in the `nil` arm.
  **`BootBad` not reused**: `clientBadWp`/`nodeBadWp` could apply `wp_OrchestratorKv`/`wp_NodeDeploymentKv` at
  `OP`/`NP := fun .. => False` (whose `Orch.specWith`/`Node.specWith` hold vacuously, a few lines each), the
  share discharged by `Hd : ¬ d.WellFormed`. Not done: it saves about ten lines of stepping per program, makes
  the malformed-deployment theorem depend on the kv dispatch (and on its `KvOnly`-shaped specs, which N7's
  all-kinds dispatch will replace), and needs a rebuild of `BootBad` (a heavy module) for no change of any
  statement. Revisit when M1's boot (§11.3 step 6) imports `KvLinked` anyway.
- **F2**: laws `deploymentRepr_workloads`, `deploymentRepr_nodes` (`deployment/Repr.lean`), `orchShare_eq`,
  `nodeShare_eq` (`client/KvDefs.lean`); the client proofs no longer unfold `deploymentRepr`/`orchShare`/`nodeShare`.
- `NodeMain`: `0 ≤ c → c < clients → c + |eps| ≤ 2^63`. `Rotate`: `xs ≠ [] → 0 ≤ i ∧ i + len ≤ 2^63`.
- `Orch.specWith` at `RunKV`'s timeout (`W64 120000000000`, `kvCheckTimeout`): weaker, and a timeout-agnostic
  P9 `Orch.spec` gives the instance by specializing.
- Not done (future work, N7): `Deployment.Node`'s converse; `MainReady`'s per-kind share.
- Go nits: `nonissues/grove-dist-rotate-doc.md`, `nonissues/grove-dist-ready-twice-kv.md` (`blocks-proof: no`).
- `etc/lean-check.py`'s misbehaviour: `notes/STATUS.md`, "`etc/lean-check.py`: a spurious kernel error".

## How to continue

- Dependencies are built: fk-lean1's worktree `/home/ubuntu/eg/wt/etcd-safe-n7kv` (at `c14f88dec2`) built
  `dist.BootBad` and its imports, 5062 jobs, exit 0 (2026-11-25). Push the branch there first
  (`fklean1-check.sh`) so the worktree has the new Spec files before `n7kv-chk.sh` checks a proof.

- Check loop: `/shared/tmp/n7kv-chk.sh <relative file> -q` (copies the file to fk-lean1's worktree
  `/home/ubuntu/eg/wt/etcd-safe-n7kv` and runs `etc/lean-check.py` there). Dependencies are built there by
  `/shared/tmp/fklean1-check.sh /shared/etcd-grove-n7kv etcd-safe-n7kv <targets>` (`FKLEAN_HOST=fk-lean1`;
  first target used: `Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.BootBad`, log
  `/shared/tmp/n7kv-build.log`).
- Order: `KvDefs`, the two deployment accessors, `Rotate`, `RunKV`, `MainReady`, `NodeMain`, `MainDeployment`,
  `NodeDeployment`, `Orchestrator`, `gen-link --deployment`, `KvLinked`; then `etc/tier-check.py --check`,
  `etc/api-check.py`, a build of `KvLinked` on fk-lean1, and a `spec-reviewer` pass on the specs.
- No axiom, no new premise; the only hypotheses are the two schemas.
