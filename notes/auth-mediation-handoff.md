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
- Next: M1 (exhaustive `v3rpc.Server.spec`, `clientPortTable`, `client_port_mediated`): STOP with the
  statements' exact text before proving past them.
