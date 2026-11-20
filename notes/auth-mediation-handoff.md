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
- M2 (in progress, 2026-11-20). Done: the JSON trust boundary in the user's smallest form
  (`Spec/encoding/json/{MarshalMember,MarshalConfigChangeContext}.lean`, axioms beside; attacked:
  survives, `notes/axiom-review/json-marshal-member.md`; Go tests `examples/authmedjson/`); the
  translation (`etcdserver.toml`: AddMember, UpdateMember, PromoteMember, promoteMember; `v3rpc.toml`:
  the five `ClusterServer` handlers, `header`, `membersToProtoMembers`, import of membership; the
  Marshal call is `Convert Member.ty go.any` then `FuncResolve encoding.json.Marshal`, the specs' shape);
  contracts `MemberContracts.lean` (`mayAddOk`, `mayPromoteOk`, `configureCcOk`, `memberSlices`,
  `addChangeType`); specs + proofs of `AddMember`, `UpdateMember`, `promoteMember` (not linked yet);
  `PromoteMember`'s metrics in `srvApplyLoopInit` (gen-init; `revokeExpiredLeases`' pattern adjusted).
- M2 next: (1) `PromoteMember`: spec drafted in `/shared/tmp/authmed/m2-next/` (contract
  `promoteHTTPOk`, no local token on the forwarded path: the leader's re-check is the contract's `Qfw`);
  contracts' answers carry `applyErrIs` (for `errors.Is`/`Error()`); proof after `LeaseRenew`'s
  forwarding loop and `processInternalRaftRequestOnce`'s `context.wp_WithTimeout`. (2) the handlers
  (`ClusterServer.Member*`): `header` over `RaftCluster.ID`/`MemberID`/`Term`/`Leader`, `togRPCError`'s
  spec, `types.NewURLs`, `membership.NewMember(AsLearner)` (names only: contracts), the contracts'
  `Qin` giving `membership.membersAt sl ms` on `nil` for `membersToProtoMembers`. (3) Link
  (`etc/gen-link.py --server` list), `etc/auth-table.txt` rows 13-17, gate baseline, tcb update (two
  new axioms: STOP already covered by the user's decision).
