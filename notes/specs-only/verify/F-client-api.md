# Final re-review: client/v3 (W0 KV, 1c lease), api/v3 Model/State, 2a, 3h, 3a/3b, 3c/3d, 2c's lease/Txn

Reviewer: fresh, independent, read-only (2026-11-09). Worktree `specs-only`, HEAD `7394a3ca7e`.
Regressions were diffed against `41c6c3a39f`. Go sources: `.lake/src/{client,server,api,pkg}`.

I formed the verdicts on RR-1 and RR1-RR4 from the specs and the Go before reading the repair
reports. I read `repair2-client.md`, `repair3-boot.md` and `repair2-relay.md` afterwards, and
only to check the disagreements (F1, F2).

## Verdicts

| batch | verdict |
|---|---|
| **W0** (client KV, `api/v3/Model`, `State`) | **PASS WITH OPEN DECISIONS.** C3 (scope: no non-`nil` empty range end) and 1.5 are unchanged. The new `adminDenied` is sound (RR2). The new ghost state in `State.lean` (`soleMember`, `urlsReserve`, the `_gen` laws) is consistent. It is not recorded in `open-questions.md` (second tier, S2). |
| **1c** (client lease) | **FAIL.** RR-1's gated row is in place. But its server-side source is false for the named user's own starter (**F1**), and the repaired snippet `ReqTTLGoneNotListedSole` does not close (**F2**). |
| **2a** (v3rpc, grpc metadata, proto) | **PASS WITH OPEN DECISIONS** (C24 / 3.2: `leasePeerURL`). RR1 and RR2 are resolved. `Server.spec` per endpoint serves its two callers. One gap is pre-existing: `AttemptTriple`'s `i = 0` arm has no server source (part of **F2**). |
| **3h** (etcdserverpb) | **PASS.** RR4's sources exist. The `endsDecoded` retirement is consistent. The watch `holds_norm` clause without `endsOk` is true. |
| **3a/3b** (apply, txn) | **PASS.** RR3 and RR4 are resolved. |
| **3c** (lease, leasehttp) | **FAIL.** `Leasehttp.ltlView` is unsound (**F3**). `lease/` itself (`NewLessor`, `Stop`, thread token) is fine. |
| **3d** (auth) | **PASS WITH OPEN DECISIONS** (`rootTokOk`, §6 F2). The `authBeCur` field-share wording is fixed. The thread-token removal is fine. |
| **2c** lease/Txn requests | **FAIL.** `EtcdServer.leaseTimeToLive.spec` is an assumed contract (names only, `etcdserver.toml:91-92`). Its gated row is false under `examples/lib/etcdstart` (**F1**). `Txn`, `LeaseGrant`, `LeaseLeases`, `SrvCallTripleF` and `srvLeaseFact` close. |

## The findings rechecked

| report | finding | status | evidence |
|---|---|---|---|
| RR-client | **RR-1**: nothing proves `leaseexpiry` once `TimeToLive`'s per-member clause is gone | **Not resolved** | The gated row is restated in three places: `viaFact` (`client/v3/ApiClient.lean:434-436`), `srvLeaseFact` (`ApiReq.lean:599-603`) and 2a's `leaseFact` (`v3rpc/Api.lean:338-340`). But the only source of the row is `EtcdServer.leaseTimeToLive.spec` (`EtcdServer__leaseTimeToLive.lean:84-92`), and its own comment (`:39-45`) says the row is false under `etcdstart`, which `leaseexpiry` uses (`leaseexpiry.go:57`). That is **F1**. Also, the repaired snippet does not close (**F2**). |
| RR-grpc-auth | **RR1**: `ReqMetadataOut` does not close | **Resolved** | `FromOutgoingContext.spec` (`grpc/metadata/FromOutgoingContext.lean:46-49`) gives `Context.ctxNoMeta ctx -∗ ⌜ok = false⌝`. That is true: `ctxNoMeta` is a `□` WP of `Value(mdOutgoingKey{})` returning `nil` (`context/Api.lean:207-211`), and grpc returns `nil, false` when the assertion fails. With `mdAtN true` (`m = null`), the check `ok \|\| md != nil` closes, and so does the rest of the snippet (`examples/specreq/grpc/grpc.go:80-95`). |
| RR-grpc-auth | **RR2**: the widened `adminDenied` is vacuous | **Resolved** | See (a) below. |
| RR-grpc-auth | **RR3**: `Txn`'s read-only path loses the `endsDecoded` share | **Resolved** | See (b) below. |
| RR-grpc-auth | **RR4**: the stringer depth premise has no source | **Resolved** | See (c) below. |

**(a) RR2.**
- `State.adminDenied who e := adminDeniedAs who e ∨ adminDeniedAs none e` (`Model.lean:877-878`). The `none` arm allows only `ErrUserEmpty`.
- 2a's `adminDenied σ who tls e` adds `adminDeniedAs tls` (`v3rpc/Api.lean:186-187`). `adminDenied_of` (`:191-192`) is a true implication under `tls = none ∨ tls = who`, which `reqPrin_of_md` gives (`:308-310`).
- This matches the code. `isPermitted` (`v3rpc/auth.go:182-188`) reads the principal through `EtcdServer.AuthInfoFromCtx` (`v3_server.go:1206-1215`):
  - auth off at `store.go:1073`: `nil`, then `AuthInfoFromTLS` under `--client-cert-auth`;
  - auth on and no token: `nil`, then the same TLS fallback;
  - otherwise the token's user.

  `IsAdminPermitted` (`store.go:915-935`) then reads the flag again and the user. So the principal it reads is `who`, `tls` or `none`. The `none` arm is admissible after any `AuthEnable`, because a lagging member can race the two reads. It is not vacuous: it fixes the error.

**(b) RR3.**
- `CheckTxnAuth.spec` (`apply/CheckTxnAuth.lean:70-82`) takes and gives back `txnReqOwn rt dq' t` at any `dq'`, with no separate share. `checkTxnPermission` and `checkTxnReqsPermission` do the same.
- `txnReqOwn_msgAt` (`etcdserverpb/Api.lean:351-353`) carries `endsOk c` at any fraction.
- So 2c's read-only `Txn` passes its own `dq` and gets `txnReqOwn r dq t` back whole.
- `endsDecoded` survives only in Changes text.

**(c) RR4.**
- **The transaction case.** `holds_depth_txn` (`etcdserverpb/Api.lean:666`) bounds the content by `txnMsgDepth t`. `t.readonly` (`Model.lean:806`) means only ranges, so `txnMsgDepth t ≤ 1 + max 1 2 = 3`. `WarnOfExpensiveReadOnlyTxnRequest` now takes that bound (`:51`), and `EtcdServer.Txn`'s sketch supplies it on the read-only path (`EtcdServer__Txn.lean:15-16`).
- **The apply case.** `irrMsgAt_msg` (`apply/Api.lean:954-957`) gives `depth c < depthMax`. That is consistent with `Unmarshal.spec`'s success case, which states the depth (`proto/Unmarshal.lean`).
- **The interceptor.** `logUnaryRequestStats` (its use of `NewLoggableTxnRequest`, `interceptor.go:163`) already takes the depth.

## New first-tier findings

### F1 (2c, reaching 1c and 2a): `EtcdServer.leaseTimeToLive.spec`'s `soleMember` row is false under `etcdstart`, and nothing states the premise it needs

**Step.** The success outcome's row is `soleMember γ -∗ ∃ j σ₂, ⌜i ≤ j ∧ σ₂.leaseAnsAt j …⌝ ∗ …` (`EtcdServer__leaseTimeToLive.lean:85-89`). The pre (`:80-81`) has no deployment premise. This file is an assumed contract (`etcdserver.toml:91-92`: "stays names only, a contract"), so it is a trusted triple.

**Evidence.**
- A sole member that is not leader at the `s.isLeader()` check (`v3_server.go:637`) calls `waitLeader`, which returns itself. It then posts to its own `PeerURLs + "/leases/internal"` (`:681-686`).
- `etcdstart` serves only `s.RaftHandler()` on the peer address (`examples/lib/etcdstart/common.go:172`). The rafthttp mux answers that path with a `404`, which `TimeToLiveHTTP` turns into `ErrLeaseNotFound` (`leasehttp/http.go:263-264`).
- So a sole member restarted in the same generation, at the same `ep` (`srvEp_gen`, `srvAt` from the new `srvFields`), and asked before its first election answers "not found" for a lease that a client's `leaseViewLb γ ep i` shows present. The row claims the lease is absent at some `j ≥ i`, which is false.
- With that row, a program that restarts the member and runs `leaseexpiry`'s check is "proved" panic-free.
- The spec says this itself (`:39-45`, and `EtcdServer__LeaseTimeToLive.lean:29`), and so does `repair3-boot.md` "New decisions 1". But `open-questions.md` has no entry for it: C24 covers only the panic on a malformed `200`, and A4 still says the clause is dropped.
- `leaseexpiry` does not restart, so its own run is safe (a single voter keeps leading). But its proof rests on a contract that is false as stated.

**Callers affected.**
- 2c's `EtcdServer.LeaseTimeToLive`;
- 2a's `LeaseServer.LeaseTimeToLive` and `leaseFact`;
- 1c's `viaFact` and the snippet `ReqTTLGoneNotListedSole`;
- `examples/etcd/leaseexpiry`.

**Fix.**
1. Put the deployment fact in the gate, so the contract is true for every `s`: `soleMember γ ∗ peerLeaseServed γ -∗ …`. Here `peerLeaseServed γ` is a persistent 2e fact: every member's peer URLs serve `leasehttp.NewHandler` of that member's lessor. It would be introduced at a peer-serving start that serves `etcdhttp.NewPeerHandler`, or a mux holding `s.LeaseHandler()`, and with it `leaseURLOf_intro` loses its free-floating `leasePeerURL` premise.
2. Make the same change in `srvLeaseFact`, `leaseFact` and `viaFact`.
3. Make `etcdstart` serve `s.LeaseHandler()` at `/leases` and `/leases/internal` beside the raft handler. That is a harness change in this repository, not in the verified code.
4. Until then, record the gap as an open user decision (A4 / C24), and mark `leaseexpiry`'s check as unproved.

The base outcome (without the row) stays true under `etcdstart`: `leaseStep`'s not-found is admissible at table 0.

### F2 (1c / 2a): nothing gives `leaseViewLb γ ep 0`, so `ReqTTLGoneNotListedSole` does not close, and `AttemptTriple`'s `i = 0` arm cannot be proved

**Step.**
- `lessor.TimeToLive.spec` is `LeaseRead.Triple` (`ApiLease.lean:254-263`), whose pre requires `leaseViewLb γ ep i` for `via = some (ep, i)`, with no `i = 0` alternative.
- The snippet (`examples/specreq/clientv3lease/member.go:83-97`) grants nothing and holds no view. So it can only use `via = none`, where `viaFact` is `True` (`ApiClient.lean:422-423`), and the panic is not excluded.
- `repair2-client.md` says it closes from "`j ≥ 0`". That assumes the `⌜i = 0⌝` alternative of `viaPre` (`ApiClient.lean:411`), but `LeaseRead.Triple` does not use `viaPre`.

**The pre-existing half** (not a regression). `AttemptTriple` (`ApiClient.lean:493-500`) admits `via = some (ep, 0)` without a view and promises `viaFact` for it. 2a's `etcdUnary` gives `leaseFact` only for `vi = some i` with `srvLeaseLbOpt γ ep vi`, that is, with a view (`v3rpc/Api.lean:349-357`). So the `i = 0` arm has no server source.

**Fix.**
- Add a law such as `leaseViewLb_zero.spec : srvEp γ ep id ⊢ leaseViewLb γ ep 0` (2e), or the same from `servesAt γ ep` (W0). It is true: every member's lessor reflects at least the initial table.
- Then drop `viaPre`'s `⌜i = 0⌝` disjunct.
- Alternatively, make the snippet grant first, as `leaseexpiry` does, and keep the view from the grant.

### F3 (3c, `leasehttp`): `ltlView` quantifies over views obtained after the answer, so `TimeToLiveHTTP.spec` (trusted) is false and can derive `False`

**Step.** `ltlView url id found := □ ∀ γ ep i, leaseURLOf γ ep url -∗ leaseViewLb γ ep i -∗ ∃ j ≥ i, … ((t id).isSome = found) …` (`leasehttp/Api.lean`, the `ltlView` def). `TimeToLiveHTTP.spec` gives it on the `200` and `404` outcomes (`TimeToLiveHTTP.lean:66-69`).

**Evidence.**
- The wand is persistent, so it can be applied later, with a view `i` that did not exist when the handler answered.
- The handler reads the lessor once (`http.go:124`), at some table `j0`. A later view `i > j0` is not bounded by that read.
- **Counterexample.**
  1. `TimeToLiveHTTP` gets a `404` for `id` (absent at `j0`).
  2. The program then grants `id`, getting `leaseViewLb γ ep jg`.
  3. Its invariant says no one revokes `id`, and leases do not expire (K2).
  4. `ltlView` at `i = jg` gives a table `j ≥ jg` without `id`.
  5. `leaseViewLb_le` with `etcdState` bounds `j`, and the invariant then contradicts it: `False`.
- `TimeToLiveHTTP` is a public function, so a program may call it directly.
- 2c's `leaseTimeToLive` contract is not affected (its `vi` is in its pre). But the trusted spec is false.

**Fix.** Take the views at the call:
- binders `γ ep (vi : Option Nat)`;
- pre `EtcdServer.srvLeaseLbOpt γ ep vi`, or 4b's own copy of it;
- post `ltlView url id found γ ep vi := match vi with | some i => □ (leaseURLOf γ ep url -∗ ∃ j ≥ i, …) | none => True`.

`leaseURLOf` may stay inside the wand: it is a run-wide fact about `url`.

## Regressions (files changed since `41c6c3a39f`)

**New ghost state.**
- **`soleMember γ`** (`State.lean:205-206`, `soleMember_intro` `ApiBoot.lean:744-746`). Sound as stated:
  - its only introduction consumes the whole `urlsReserve γ 1`;
  - `urlsReserve` is fractional and only `cluster_alloc` mints it;
  - `urls_reserve` spends a share and gives none back;
  - every member addition takes a `urlsRight` (`ApiClient.lean:620`, `EtcdServer__AddMember`).
  
  I found no way to prove `False`.
  
  Uncertain: the doc relies on a removal of the only voter being refused or panicking (`nonissues/raft-remove-last-voter-panic.md`). A panicking path would need a premise somewhere in raft or 2e. I did not check where.
- **`urlsReserve`** (`State.lean:215-216`). Sound. It has no validity law, which is harmless: nothing can rebuild `1` from spent shares.
- **`srvEp`/`srvAt`** (`ApiBoot.lean:380-390`, `:754-775`). Sound:
  - `srvEp_reserve` consumes `Http.addrFree ep`, and `addrFree` is the run's (`net/http/Api.lean:380-381`), so there is one binding per run and `srvEp_agree` cannot be split;
  - `srvAt` is transparent.

  Uncertain: an old server object's `leasehttp` handler still serving on a peer listener after `Stop` would answer from a lessor behind the new object's. `leaseURLOf`'s "whichever server object" assumes the listener closes with the server.
- **`leaseURLOf`** (`leasehttp/Api.lean`; `leaseURLOf_intro`, `ApiBoot.lean:790-793`). Plausible: peer-URL sets are single-use. It inherits F1's deployment premise.
- **`ltlView`**: unsound (**F3**).
- **The `_gen` laws** (`State.lean:265-301`). Plausible if the cluster's invariants and ghost names are in `GooseGlobalGS`. Uncertain: I did not check that Perennial's invariants are global. No exclusivity clash: within one generation, rewriting `hG` is an equivalence.

**`Server.spec` per endpoint** (`v3rpc/Server.lean:44-49`).
- Both callers can establish `srvAt s γ ep`: `etcdstart.Serve` and embed's `serveClients`, the latter once per client URL, each reserved with `srvEp_reserve` at the same id.
- The snippets `v3rpc/serve.go` and `etcdserverboot/boot.go` are updated.
- Uncertain: an in-process `v3client` over `NewQuotaLeaseServer`'s handlers now needs some `srvAt s γ ep`. An embed member always serves one, but a program with no served address could not call the lease handlers.

**`EtcdServer.Txn`, `LeaseGrant`, `LeaseLeases`.**
- `SrvCallTripleF` with `srvLeaseFact` closes from 2c's sketches.
- The grant's view comes from the local apply (the wait registry is triggered at apply).
- `Leases` reads `s.lessor.Leases()` (`v3_server.go:737`), which moves only forward within a generation (`Close` commits the batch; there is no `leaseViewLb_gen`).

**The rest.**
- `lease/` (`NewLessor` returns the caller's `threadTok`; `Stop` returns none): consistent with `wp_fork_tok`, whose forked body gets its own token (`Lifting.lean:1964-1966`).
- `auth/` token-provider token removal: likewise.
- `etcdserverpb` `holds_norm`'s watch clause without `endsOk`: true, because `watchReqOwn_unfold` models the create's end as bytes, and `nil` and `[]` agree.

## Second tier

- **S1.** Stale wording:
  - `LeaseServer__LeaseTimeToLive.lean:14` ("2c's lease specs give no per-member view yet, for `Grant` and `Leases` either");
  - `ReqGoneNotListed`'s Users line (`member.go:39-41`) still has the pre-gate rationale.
- **S2.** New client-visible ghost state (`soleMember`, `urlsReserve`, `srvEp`/`srvAt`, the one-member-id-per-address cost) is recorded only in repair reports. `open-questions.md` A4 still says the `TimeToLive` clause is dropped. These belong with the user's decisions (A4, A15).
- **S3.** The `nonissues/etcd-admin-check-authenable-race.md` wording now matches `adminDenied`. No action.

## Counts

- Findings rechecked: 5.
  - Resolved: RR1, RR2, RR3, RR4.
  - Not resolved: RR-1 (F1, F2).
- New first-tier findings: 3 (F1, F2, F3). F2's `AttemptTriple` half is pre-existing.
- Second tier: 3. Uncertain notes: 4.
- Spec files rechecked: the 60 files changed since `41c6c3a39f` in the area, plus the callees they cite (`ApiBoot` `srvEp`/`soleMember_intro`/`leaseURLOf_intro`, `net/http` `addrFree`, `proto` `Unmarshal`).
- Snippets rechecked:
  - close: `grpc/metadata-out`, `clientv3lease/grant-then-list-one-member`, `gone-not-listed`, `apply/ReqCheckTxnAuth`, `v3rpc/serve`;
  - do not close: `clientv3lease/ttl-gone-not-listed-sole` (F2, F1).
- No bug in the Go code under verification. Nothing for `issues/`. F1's 404 is the harness's (`examples/lib/etcdstart`), and the spec itself records it.
