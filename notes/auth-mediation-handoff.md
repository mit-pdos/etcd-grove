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
- M2, second session (2026-11-20). Committed, build `20261120-201939-1779142` (after the
  etcdserverpb regeneration: exit 1, only `membersToProtoMembers` failing): etcdserverpb's Cluster
  messages translated (`etcdserverpb.toml`; they were axiomatized types with `sorry` instances, so no
  handler could be proved); `v3rpc/InvCluster.lean` (`clusterServerIs`, `clusterHdrOk`,
  `memberOutC`) and `MemberContracts.lean`'s `memChkAns`, `memCfgAns` (built); specs of
  `ClusterServer.{header,MemberRemove,MemberList,MemberUpdate}` and `membersToProtoMembers`;
  `header`'s proof (built). **Not yet checked**: the proofs of `MemberRemove`, `MemberList`,
  `MemberUpdate` (drafts, never compiled: not reached by the build's targets until linked; check each
  with `etc/lean-check.py`) and `membersToProtoMembers` (line 93: `wp_auto: no progress` at the
  `&pb.Member{...}` literal; written when `pb.Member` was axiomatized, retry now; then the
  `wp_store_slice_index` into `protoMembs[i]` and the loop's close, drafted below it).
- M2 next: (1) **`PromoteMember` is blocked** (reported to etcd-grove-03): its
  `learnerPromoteFailed.WithLabelValues(err.Error())` panics unless the message is valid UTF-8, and
  the guard's error (`checkMembershipOperationPermission`'s `adminOutC`) carries no message fact
  (`adminWhy` is `True` with auth off). Recommended: strengthen the guard's post with `authErrVarIs
  err` (its errors are `AuthInfoFromCtx`'s `authApplyErrIs` and `IsAdminPermitted`'s; with auth off
  `nil`), whose messages are `auth.authErrMsgs` literals (`authErrVarIs_cell`); the contracts'
  answers then add a UTF-8 message fact. It changes a row spec of `client_port_mediated` (stronger):
  a hard stop. Draft contract `promoteHTTPOk`: `/shared/tmp/authmed/m2-next/`. (2) `MemberAdd`:
  `types.NewURLs`'s axiom covers only non-empty plain `http://host:port` lists (premise on the
  request's peer URLs, recorded as the margin) and `membership.NewMember(AsLearner)` are names only
  (a contract `newMemberOk learner`); the premises `∀ id, configureCcOk ...` and `∀ memb ps,
  mayAddOk ...` (the member's id is computed). (3) `NewClusterServer`'s post: `clusterServerIs` (a
  stronger post). (4) Link (`etc/gen-link.py --server` list), `etc/auth-table.txt` rows 13-17
  (13, 15 contract once MemberAdd/Update are linked; 14 contract; 16 e2e; 17 contract after
  PromoteMember), `ClientPortTable.lean`, gate baseline, tcb update (the two JSON axioms).
