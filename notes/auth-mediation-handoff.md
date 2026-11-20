# auth-mediation handoff (stages M0-M4 of notes/auth-mediation-scope.md)

## START HERE

- Worktree `/shared/etcd-grove-authmed2`, branch `auth-mediation` (off lean `d45f8b140e`), agent of
  etcd-grove-03. Perennial pin c44b74871: `--packages=/shared/tmp/manifest-c44.json`,
  `PERENNIAL_DIR=/shared/perennial-c44b74871`. Decisions: `questions.md` (untracked, worktree root).
- The Scope (approved 2026-11-20): `notes/auth-mediation-scope.md` (D2 b-table, D3 Lock/Election
  excluded, D4 local JSON trust-boundary spec, D5 M4 now / M5 deferred, D6 "every gRPC request").
  The gateway finding is private: never describe it in a public file.
- M0 (done): `etc/authmed/main.go` lists the client port's registrations from the Go source at the
  pin; `etc/auth-table.txt` classifies each; `etc/auth-mediation-check.py --check` (in `etc/gates.sh`,
  sec_goose, and CI) checks them against the specs and `etc/auth-mediation-baseline.txt`.
  Matrix corrections in `notes/auth-matrix.md`; the v3lock issue's front matter (`upstream: known`).
  Row 12 (LeaseKeepAlive) confirmed: `kaStreamSpec` gives every response `kaDn`, the renewal's
  `leaseCheckFrom` verdict at its request's bounds.
- M1 (statements written and proved, at the STOP): `etcdserverpbDescs` (cache/v3/Base.lean) and
  `svcDescsOk` (BaseStart) state every descriptor exactly (Cluster, Maintenance, KV's and
  Maintenance's streams with handlers; `pbDescOk`, `descOk` deleted); `v3rpc.serverRegsOk`
  (InvGrpcStart) the exact registrations; `v3rpc.Server.spec` posts it (+ `pc pm`); consumers use
  `serverRegsOk_sub`; `ClientPortTable.lean` (defs) the Lean table; `client_port_mediated`
  (v3rpc/Results.lean). Gate checks the Lean table against etc/auth-table.txt.
  The Base change rebuilds ~7400 modules: next build is a full one.
- Next after the user's go: full timed build, then M2 (Cluster handlers + JSON spec).
