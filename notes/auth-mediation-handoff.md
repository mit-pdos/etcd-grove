# auth-mediation handoff (stages M0-M4 of notes/auth-mediation-scope.md)

## START HERE

- **M4 landed on lean** (`dc24475728`). **M3 in progress** (2026-11-21): worktree `/shared/etcd-grove-authm3fix`,
  branch `auth-m3-forkfix` (off lean `dc24475728`), agent of etcd-grove-03. Pin c8e356cb1:
  `--packages=/shared/tmp/manifest-c8e.json`, `PERENNIAL_DIR=/shared/perennial-c8e356cb1`. Decisions: `questions.md`
  (untracked, worktree root; Q4 decided: option (i), the fork fix).
- Fork: etcd pin `4416a5786` (branch `goose-lean-rangestream-clone` of `upamanyus/etcd`, local checkout
  `/shared/tmp/authm3fix/etcd`, upstream etcd-io/etcd@9acc0ebe37 cherry-picked): NOT pushed; the user pushes it
  (`git -C /shared/tmp/authm3fix/etcd push origin goose-lean-rangestream-clone`) before the coordinator lands.
  Translate with `etc/goose.py --project etcd --src etcd=/shared/tmp/authm3fix/etcd --perennial /shared/perennial-c8e356cb1`.
  `TestConcurrentKeysOnly` passes with `-race` at the fork (rerun 2026-11-21).
- M3 as done: `headerFillingRangeStream.Context` translated (`v3rpc.toml`); `txn.rangeRequestAt r dq o`
  (`txn/RequestAt.lean`) and the readers over it (getters `GetKey`/`GetLimit`/`GetRevision` at `↦{dq}`,
  `HasRevisionFilters`, `checkRangeRequest`, `checkRangeStreamRequest`; ledger 2026-11-21); proofs
  `EtcdServer__RangeStream.lean` (over the axiom `EtcdServer.rangeStream.wp_proof` and `doSerialize`) and
  `kvServer__RangeStream.lean` (spec new, vocabulary `v3rpc/RangeStreamOut.lean`: `rangeChunkOut`); Links
  (`--server`, `--v3rpc`); row 2 `e2e` (`etc/auth-table.txt`, `ClientPortTable.lean`, `Results.lean`);
  `notes/audit.md` row. The axiom joins the linked trust base (approved: Q1 option (B)).
- Checked: full timed build `20261121-142116-1287569` green (at lean `3ac6cb4031` merged); tcb `--check --update`:
  +1 axiom `EtcdServer.rangeStream.wp_proof` (533 axioms, 0 sorries); collections `server`, `v3rpc` +1 (updated), 69
  unchanged; `etc/auth-mediation-check.py --check --update` (row 2 `none` -> `e2e`). Until the fork commit is pushed,
  the checks that clone etcd (`auth-mediation-check`, `goose.py --check`) need `.lake/goose/etcd` at `4416a5786`
  (`git -C .lake/goose/etcd fetch /shared/tmp/authm3fix/etcd 4416a5786... && git -C .lake/goose/etcd checkout --detach FETCH_HEAD`).
- `etc/gates.sh` (2026-11-21, first run, log `/shared/tmp/authm3fix/gates.log`): only `axiom-tok` and its selftest
  failed: rule 5, 48 axioms tainted by M3's new axiom `EtcdServer.rangeStream.wp_proof` (its walk through
  `isServerReqM`/`isServerReadM` capped and truncated; rule-3/7 keys identical to `leaseTimeToLive`'s, no mint). Fixed
  by three allow-list entries in `etc/axiom-tok-allow.txt`, copies of `leaseTimeToLive`'s (approved by the user,
  2026-11-21, via etcd-grove-03; questions.md Q5). Gates rerun after it: see the commit after this one / the report.
  **At the LAND STOP**: the coordinator lands (the fork branch is pushed).

## M4 proposal (approved 2026-11-21; implemented in `a351492b8d`)

The refusal reason for the admin rows (28-42) reaches the proposer in two definitions; no spec text changes,
the specs that mention them get stronger posts.

1. `adminTieAr` (`KVAuthModel.lean:1927`). Old: `⌜needAdminPermission rq = false ∨ ∀ o b, out ≠ .dispatched o b⌝
   ∨ ∃ v, ar ↦□ v ∗ ⌜v.Err' = nil → adminStepOk rq st st'⌝` (a rejected outcome: nothing). New:
   `⌜needAdminPermission rq = false ∨ out = .skipped⌝ ∨
    ⌜out = .rejected ∧ ¬ auth.adminOk st (some (auth.authInfoM (apply.principalOf rq)))⌝ ∨
    (⌜∃ o b, out = .dispatched o b⌝ ∗ ∃ v, ar ↦□ v ∗ ⌜v.Err' = nil → adminStepOk rq st st'⌝)`.
   Source: `adminOut_model` (`ApplyTieOn.lean:253`) already has `adminRejL (.on γa) hs rq` at `hs.getLast? = some st`
   (`hrej`), i.e. `¬ adminOk st ..`; its rejected case changes from `ileft` to the new middle disjunct.
2. `adminOutOn`'s error branch (`AdminOn.lean:185-188`). Old: `appliedErr E rq' F err` (the result's `Err` is `err`,
   no reason). New: `appliedErr E rq' F err ∗ ∃ L, srvRLogLb ρ.raft L ∗ adminTieM true ρ.kv rq' L ar out` for the
   result `ar` and outcome `out` the waiter delivered (exact form fixed at the Freeze: the waiter's `resultIsWOn`
   carries `adminTieAr` at the committed prefix's state; `processInternalRaftRequestOnce`'s error branch passes
   `resultIs` today and would pass the `On` form).
   Specs whose posts change (stronger): the thirteen admin entry points' `*OutOn` definitions in
   `Spec/.../etcdserver/EtcdServer__<M>.lean` (`userAddOutOn`, ...), `processInternalRaftRequestOnce.spec`'s
   mode-`on` result, and through them the admin rows of `client_port_mediated`; `apply.admin_rejected_why` unchanged.

## M2 record (done, on lean)


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
- M2, fourth session (2026-11-20/21): `EtcdServer.MemberList.spec` and `ClusterServer.MemberList.spec`
  restated in place over `isServerReqM/ReadM E.authOn` (+ `kvDep .. (kvStM E.authOn γr.kv)`; decided by
  etcd-grove-03, ledger); row 16 `server` -> `e2e` (`19c4837cea`). lean `03a1092f20` merged: build
  `20261120-222511-2348731` green, tcb baseline 654 -> 657 (the two JSON specs + `context.madeCancelCtx_of_isCancelCtx`,
  reached through `PromoteMember`'s `ctxDoneErr_of_isContext`), collections `server` +3, `v3rpc` +4 (also
  `types.NewURLs`, via MemberAdd), others unchanged (`46dc96a876`); `etc/gates.sh` all passed there.
  Then lean `f5cf653a85` (merge-origin13) merged (`v3rpc.lean` regenerated by goose, PkgTables/InitLinked by
  gen-init, ledger both sides): its full build was STOPPED by the coordinator's pause (exit 143, modules kept).
- Next (on "resume"): full timed build; tcb `--check` (re-`--update` if lean's delta moved the counts) and the
  70 collections; `etc/gates.sh` (LAKE_PACKAGES, PERENNIAL_DIR, PATH with go); the STATUS entry (front of the
  line, oldest to status-history: check `wc -l` >= lean's); report the M2 land stop and STOP.
- Then M3 (RangeStream), M4 (STOP first with the exported specs' old -> new).
