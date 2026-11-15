# kvraftN: handoff

State (2026-11-15): Scope written (`notes/kvraftN-scope.md`), waiting for etcd-grove-81's decisions
(`questions.md`). No Lean or Go change. Probe: `/shared/tmp/kvraftN/KvraftNProbe.lean` (copy it into the tree
as a module when the generic lemmas are needed; it checks with `LAKE_OPTS=--packages=/shared/tmp/manifest-e9e.json
etc/lean-check.py -a`).

Next, in order (after the decisions): kv (Go `MainN`, tests, `etc/goose.py --project` for the examples project;
`RKVNames.voters`; `StartCluster` over `vs`; `MainN`/`Main`; adequacy; Results; collection), then kvreconf,
then kvdurable (if R2).

Pitfalls: keep the voter lists symbolic (no `decide` on `kvBootVoters k`, no bare `iframe` over `[∗list]` of them);
builds under the flock and the 64G cap; Go with GOWORK=off and the 32G cap.
