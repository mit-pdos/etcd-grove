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

## The proofs: state at handoff (NONE CHECKED YET)

All drafted blind, never compiled (the fk-lean1 worktree was still seeding when the context ran out):
`Proof/.../dist/deployment/Deployment__{Endpoints,Node}.lean`, `Proof/.../dist/client/{Rotate,RunKV,MainReady,
MainDeployment,Orchestrator,NodeMain,NodeDeployment,KvLinked}.lean`, `KvDefs.lean`'s lemmas.
- Complete drafts (expect tactic fixes): `Deployment__Endpoints` (copied from `memberIDs.lean`'s loop),
  `RunKV`, `MainReady`, `Orchestrator`, `NodeMain`, `KvDefs` (`kvOnly_bounds`: check the conjunct count of
  `typed.Deployment.WellFormed`, 21).
- `sorry` placeholders left (must go before landing): `Deployment__Node` (the loop body and exit; pure lemmas
  `nodeEntries_cons_get`, `zip_drop_cons` drafted for the invariant
  `d.nodeList[n0]? = (((ws.zip ns).drop j).flatMap nodeEntries)[k]?`); `Rotate` (the index `srem` lemma and the
  body: store at `j` with `wp_store_slice_index`, invariant `outL[m]? = rotateL[m]?` for `m < j`);
  `MainDeployment` (after the `WellFormed` check: the `j` range check, load
  `Workloads[j]` and `Nodes[j]` from `deploymentRepr`, `Endpoints` through the pointer method, then `hMR` with
  `orchShare` unfolded); `NodeDeployment` (after the check: `Herr` gives `d.WellFormed`, `kvOnly_bounds`,
  `hNd`, `¬ok` return, loads, `Endpoints`, persist the slice, `hNM` with `nodeShare` unfolded).
- Open question for the method calls: the code calls `MethodResolve (PointerType Deployment.ty) "Endpoints"`
  on the local `d`; the specs are on the value receiver (`#(methods Deployment.ty …)`), as `fields.Set.Get`.
- `KvLinked.lean` (linking tier by name): `wp_OrchestratorKv OP hOrch`, `wp_NodeDeploymentKv NP hNode`, the
  results step 6 uses. Needs `deployment/Link.lean` regenerated: `etc/link-lean-first-deployment.txt` already
  lists `deployment_Deployment__Endpoints`/`__Node`; run `etc/gen-link.py --deployment`.

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
