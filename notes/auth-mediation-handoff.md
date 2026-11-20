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
- M1 (approved by the user 2026-11-20, at the land stop): `etcdserverpbDescs` (cache/v3/Base.lean) and
  `svcDescsOk` (BaseStart) state every descriptor exactly; `v3rpc.serverRegsOk` (InvGrpcStart) the
  exact registrations; `v3rpc.Server.spec` posts it; `ClientPortTable.lean` the Lean table;
  `client_port_mediated` (v3rpc/Results.lean). lean `951d520138` merged; builds
  `20261120-182540-1298292` + `20261120-184907-1359064`; tcb unchanged; etc/gates.sh passes.
- M2 next (after the land): the JSON trust-boundary specs are drafted and attacked, awaiting the
  STOP's answer: `/shared/tmp/authmed/m2-draft/MarshalMember.lean` (two specs, `MarshalMember` and
  `MarshalConfigChangeContext`, beside the k8s token spec; opaque outputs with a `PeerURLs` nil flag);
  attack round 1 refuted the flagless draft (nil vs empty `PeerURLs`), round 2 sound; the Go tests to
  commit with it (`examples/...` or beside the axiom): `/shared/tmp/authmed/m2-draft/jsontests/`.
  Then: translate `EtcdServer.AddMember/UpdateMember/PromoteMember/promoteMember` and the five
  `ClusterServer` handlers (re-check the Marshal call's Goose shape), specs over contracts for
  `mayAddMember`, `configure`, `NewURLs`/`NewMember`, `promoteMemberHTTP`.
