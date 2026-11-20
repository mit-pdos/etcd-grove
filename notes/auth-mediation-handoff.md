# auth-mediation handoff (stages M0-M4 of notes/auth-mediation-scope.md)

## START HERE

- Worktree `/shared/etcd-grove-authmed2`, branch `auth-mediation` (off lean `d45f8b140e`), agent of
  etcd-grove-03. Perennial pin c44b74871: `--packages=/shared/tmp/manifest-c44.json`,
  `PERENNIAL_DIR=/shared/perennial-c44b74871`. Decisions: `questions.md` (untracked, worktree root).
- The Scope (approved 2026-11-20): `notes/auth-mediation-scope.md` (D2 b-table, D3 Lock/Election
  excluded, D4 local JSON trust-boundary spec, D5 M4 now / M5 deferred, D6 "every gRPC request").
  The gateway finding is private: never describe it in a public file.
- M0, M1 done (M1 approved by the user 2026-11-20): the gate `etc/auth-mediation-check.py` over
  `etc/auth-table.txt`; `v3rpc.Server.spec`'s exact registrations; `client_port_mediated`
  (v3rpc/Results.lean). Details: `git log` and `notes/auth-mediation-scope.md`.
- M2 (in progress, 2026-11-20). Done: the JSON trust boundary in the user's smallest form
  (`Spec/encoding/json/{MarshalMember,MarshalConfigChangeContext}.lean`, axioms beside; attacked:
  survives, `notes/axiom-review/json-marshal-member.md`; Go tests `examples/authmedjson/`); the
  translation (`etcdserver.toml`: AddMember, UpdateMember, PromoteMember, promoteMember; `v3rpc.toml`:
  the five `ClusterServer` handlers, `header`, `membersToProtoMembers`, import of membership; the
  Marshal call is `Convert Member.ty go.any` then `FuncResolve encoding.json.Marshal`, the specs' shape);
  contracts `MemberContracts.lean` (`mayAddOk`, `mayPromoteOk`, `configureCcOk`, `memberSlices`,
  `addChangeType`); specs + proofs of `AddMember`, `UpdateMember`, `promoteMember` (not linked yet);
  `PromoteMember`'s metrics in `srvApplyLoopInit` (gen-init; `revokeExpiredLeases`' pattern adjusted).
- M2, third session (2026-11-20): done, see `git log` (commits `b38c566b57`..): the four handler drafts and
  `membersToProtoMembers` proved; the guard's post `authErrVarIs` (decided by etcd-grove-03); contracts'
  answers carry a UTF-8 message (`errMsgP`, moved to `etcdserver/ErrMsg.lean`); `EtcdServer.PromoteMember`
  (forwarding as `LeaseRenew`'s, `promoteHTTPOk` contract) and `ClusterServer.MemberPromote`;
  `ClusterServer.MemberAdd` (margin: plain `http://host:port` peer URLs, a premise; `newMemberOk` contract);
  `NewClusterServer` posts `clusterServerIs`; Links (`--server`, `--v3rpc`); table rows 13, 14, 15, 17
  `contract`; row 16 (MemberList) stays `server` (its server spec takes `isServerReq`, auth off: ledger
  entry, reported); gate baseline; lean merged (`5ebda1039e`).
- State at handoff: full timed build started after the merge (log `/shared/tmp/authmed/build1.log`,
  not seeded: incremental from this worktree's build); its result is in the report to etcd-grove-03.
- Next (M2 land stop): if the build failed, fix (likely candidates: importers of `v3rpc.errMsgP`, now in
  `etcdserver/ErrMsg.lean`; `Server.lean` uses `NewClusterServer` as `%pc -`); then tcb-report `--check
  --update` (expected delta: +2 axioms, the JSON Marshal specs, in the server/v3rpc collections), collections
  `--check --update`, every gen-link mode (`--server`, `--v3rpc` regenerated after the merge?), interfaces,
  tier, gen-init/goose `--check`, mode, bounds, axiom-tok, `etc/auth-mediation-check.py --check`; a STATUS
  entry (front of "Last updated", oldest to status-history, append-only); report and STOP (no land.sh).
- Then M3 (RangeStream), M4 (STOP first with the exported specs' old -> new).
