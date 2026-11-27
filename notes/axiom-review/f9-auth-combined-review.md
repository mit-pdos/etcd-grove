# F9: one combined review of the auth-on interim axioms, `Lease_TimeToLiveOn_dist`, `Serve_dist`, `NewServer_dist` (2026-11-26)

This review used the `axiom` skill. It is read-only on the Lean tree: branch `etcd-safe-f7-rlog` at `c5b8bb0348`, in
the worktree `/shared/etcd-grove-f9rev`. The Go is the etcd fork at `etc/goose.py`'s pin `df6af0c36a6b`, with grpc
v1.84 and go1.27.3. The question: do these axioms, taken together, prove a no-panic triple for a Go program over that
etcd that panics when run? The earlier piecewise reviews (`f7-*.md`, `watchon-dist.md`, `f7-distdiff-review.md`)
were read for context only. Every verdict below was reached afresh.

## Summary (for the packet's §2–3)

**No counterexample.** No statement needs to change. The fixes are docstring fixes (D1–D4) and corrected texts for
two `axiom-tok` justifications (J1, J2).

| axiom | verdict | reason (section) |
|---|---|---|
| `KV_PutOn_dist`, `KV_DeleteOn_dist` | **SOUND** | The grant is the apply-time check, the same at every member, and the update is persistent and fires at most once. A lagging member or a race with `AuthEnable` gives no success the model refuses (Go tests [lag] and [race], §2) |
| `KV_GetOn_dist` | **SOUND** | The linearizable read waits for apply ≥ read index ≥ every commit before the call. So the check's state follows the caller's `L₀` even at a lagging member (Go test [lag]: 0 of 1,538 anonymous or forbidden reads served). `authFloorD`'s update form is right (§2.3) |
| `Txn_CommitOn_dist` (with `txnNestOk`) | **SOUND; docstring fix D3** | Nested writes are checked at apply by `checkTxnReqsPermission`, recursively. A nested write proposed at a lagging member, or racing `AuthEnable`, is refused (tests [lag], [race]). The docstring's last line, "Unchanged since", is stale: it was widened twice |
| `WatchOn_dist` | **SOUND; docstring fixes D1, D2** | The floor at every endpoint closes the one real lag hole, which is watch-only: a lagging member passes creates at its old state (`watchon-dist.md` [lag]). `watchon-dist.md`'s F4 and F5, deferred "to the adoption commit", were never applied, and the axiom is now in `etcd_safe_nocrash`'s trust base (S13) |
| `New_user_dist` | **SOUND** | `Authenticate` runs `linearizableReadNotify` before `CheckPassword`. The post's member-local disjuncts (`passwordChecked` or `enabledVerdict … false`) hold at the member that answered. The not-enabled arm is weak (true of the boot state) and asserts nothing a program can contradict |
| `Auth_AuthEnable_dist`, `Auth_RoleAdd_dist`, `Auth_RoleGrantPermission_dist`, `Auth_UserAdd_dist`, `Auth_UserGrantRole_dist` | **SOUND** | The apply-time `IsAdminPermitted`, at the header the proposing member stamped: `""` when it lags with auth off, which apply then refuses. The name bounds rule out `issues/etcd-auth-useradd-long-name-fatal`. `adminRepliedD` reads no member name (§2.4) |
| `Lease_TimeToLiveOn_dist` | **SOUND** | It claims only the echoed `ID` and the member's own check over its own lessor's keys at `j ≥ m₀`. It says nothing of `Keys`, `TTL` or `GrantedTTL`, so it does not claim past `issues/etcd-lease-timetolive-keys-toctou.md` (§3) |
| `Serve_dist` | **SOUND; docstring fixes D1, D4** | Condition C holds. Its auth-on branch ties `Γ.au mid`/`Γ.ls mid` to the member's exclusive resources. Every route that serves `etcdSvc Γ mid` needs it. The panic paths a client can reach are excluded: the closed-backend panic is fixed in the fork (`d52eec43e`), and peers are only `PeerServe_dist`. But its "who calls" list names only the auth-off contracts (D4), not `WatchOn_dist`'s streams (D1, `watchon-dist.md` F5) |
| `NewServer_dist` | **SOUND** | Unchanged in substance since `f7-combined.md` §1, apart from `etcdURLsFit` restored (`812a1bf455`, a stronger premise). `authNamesFreshD γa` and `Hlslot` are what make the Serve tie exclusive |

| axiom-tok justification | verdict |
|---|---|
| `Serve_dist` (entry line 209 and its section header, lines 189–208) | **Keys OK** (re-walked: the entry matches). **Text: corrected (J1)**. The header still describes the old statement: it says Serve consumes `etcdstart.memberUp`, `etcdAddrAt a γE mid` and `envAt γE ν`. The entry's reason says "the proved in-process `Serve.wp_proof` over the same handles", which the header itself denies |
| `New_user_dist` (line 364) | **Keys OK** (re-walked: rule 7 `∃ P` ×7 and `∃ scd`, nothing else). **Text: corrected (J2)**. "No level token in its pre or post" is false: its pre takes `levelTok 0` and its post returns it, and the walk counts `L:0` consumed 9, produced 9. `scd` is not "the context `getToken` makes inside the call": it is the returned lessor's stop context |
| F7 S13 block (lines 351–373) | **OK.** Each key matches the walk (`f7-auth-axiom-tok.md`, and the S14 run on fk-lean `~/eg/logs/f7rl-atok{,2}.log`: `axiom-tok: ok`). The counts are the auth-off siblings' |
| F7 S14 block (lines 374–391) | **OK.** The five admin axioms, rule 2 `8/1` and rule 7 `P`, as `KV_PutOn_dist`'s. The pre-entry walk (`f7rl-atok.log`) shows exactly these findings |

## 1. Method

- I read the statements at `c5b8bb0348`: `Spec/.../etcd/dist/{KV*On,TxnCommitOn,WatchOn,NewUser,Auth*,LeaseTimeToLiveOn,Serve,NewServer}Dist.lean`
  and their `Proof/` docstrings, the vocabulary `AuthViewDist.lean`, `MemberLessor.lean` (`memberUpL`/`memberUpOnL`) and
  `etc/axiom-tok-allow.txt`.
- **The walk, re-run.** `etc/AxiomTokCheck.lean` on `New_user_dist` and `Serve_dist`, judged by `etc/axiom-tok-check.py
  --reuse-raw -v --all` on fk-lean (`~/eg/tmp/f9rev-atok.sh`, log `~/eg/logs/f9rev.{log,raw}`). It ran in the
  `etcd-safe-f7-rlog` worktree, whose `NewUserDist.lean`, `ServeDist.lean`, `AuthViewDist.lean` and allow file are
  byte-identical to `c5b8bb0348`'s (md5 checked).
- **Go tests** (`f9-auth-combined-gotest/`, `go test -run TestF9`, 3-member integration cluster, simple tokens; output
  in `output.txt`):
  - **[lag]** `TestF9LagWritesReads`. A follower is stopped before the set-up and `AuthEnable` and restarted after
    60 root puts (`SnapshotCount 10`: it catches up by a snapshot). From its restart on, an anonymous client and
    `u`'s client (allowed only `[a, b)`) try `Put c/…`, a nested `Txn` putting `c/n…`, and a linearizable `Get c/1`
    at that member.
  - **[race]** `TestF9EnableRace`. Two anonymous workers per member run the same three operations while `AuthEnable`
    is issued. Afterwards a root `Put` gives the post-enable revision `R`.
- **Results.** [lag]: 4,617 attempts, **0 successes**: `user name is empty` ×939 per operation, `permission denied`
  ×599 per operation, 3 timeouts during catch-up. Afterwards `c/` holds only `c/1`. [race]: 3,990 operations, 502
  succeeded before the enable returned, all applied below `R`. **0 successes sent after the enable returned, and 0
  applied at or after `R`**.

## 2. The interactions

### 2.1 Auth-state changes racing with reads, writes and watches on other members

- **Writes** (`KV_PutOn`, `KV_DeleteOn`, the write arm of `Txn_CommitOn`). In Go the permission check is at apply.
  `authApplierV3` calls `isOpPermitted` and `checkTxnReqsPermission` with the header the proposing member stamped.
  Every member applies the same entry against the same auth state. With auth enabled, a header revision of 0 (no
  user) gives `ErrUserEmpty`, and a stale one gives `ErrAuthOldRevision`. The model is `grantedAt Γ.kv srvAuthSt0
  (withHeader rq hm) L`, the history after the requested prefix before the entry, with `userOk P hm.username`. So a
  write racing `AuthEnable` succeeds iff its entry precedes the enable. Test [race] shows exactly that.
- **The persistent update** (`writeAuD`'s `□`) is offered to several attempts and fires at most once. The retry
  interceptor resends a mutable RPC only after a token refresh (`ErrInvalidAuthToken`, `ErrUserEmpty`) or a send
  that never left. Each of those is refused before or at apply, with no step. So two applied attempts are
  impossible.
- **Reads** (`KV_GetOn`, the read-only arm of `Txn_CommitOn`). A linearizable read first waits until the member has
  applied up to a read index at least every commit before the call, and then checks at the member's current state.
  `readCheckedD`'s `L ⊒ L₀` (with `srvReqLogLb γR L`) and `authFloorD` follow. Test [lag]: no read was served at the
  lagging member's old state.
- **Watches** (`WatchOn_dist`). A create is checked at the member's current state with no read barrier. So a lagging
  member passes an anonymous create at its pre-enable state (`watchon-dist.md` [lag]: 2 of 13,556). `watchFloorsD`
  asks for a floor at *every* endpoint's member, which excludes this. The floor is the serving member's own
  (addresses are set once, and `etcdSvc Γ mid` is per member). The row claims only the create's check: a later
  revoke does not end a stream in Go, and the axiom does not say it does.
- **Admin calls racing data calls.** These go through the single history `Γ.kv.hist` (`histAu`), tied to every
  member's `authStateAt (Γ.au mid)` by `Serve_dist`'s `memberUpOnL` (`ρ.rd.kv.hist = Γ.kv.hist`). No admin axiom
  grants a member-local fact. So no admin step can be "seen" at one member's names and not at another's beyond what
  the floors state.

### 2.2 Token and metadata handling (`outTokOk`, `outTokOkS`, `principalOf`)

- **Every way a call can carry an issued token of another principal is closed:**
  - `cfg.Token' = []`, in `userClientAt`, `authClientAt`, `leaseUserAt` and `clientCfgOk`;
  - `outTokOk` covers both keys the server reads, `token` and `authorization` with `Bearer ` (`f7-s5-review.md` §1).
    For a named principal it forbids both keys outright;
  - outgoing metadata exists only through grpc's own builders (`metadata.outMD_ownKey` needs `builtRawMDRaw`, which
    only `AppendToOutgoingContext` makes, lowercasing its keys; `NewOutgoingContext` has no spec), so an uppercase
    `Token` cannot reach the wire behind a literal-key check (`f7-s5-confirm.md`);
  - `outTokOkS` quantifies over every metadata of the watch's stream key, which closes the `fmt`-collision case
    (`watchon-dist.md` (d)).
- **A refreshed token** is the token of `cfg`'s user (`getToken` with `cfg.Username`/`Password`). So the principal
  stays `principalOf cfg` across `ErrUserEmpty`/`ErrInvalidAuthToken` refreshes, and also when `New` ran while auth
  was off (no token: the first refused call refreshes it).
- **Simple tokens** are assigned by apply on every member to the same user. A token from member A is either accepted
  at B as the same user or refused (`ErrInvalidAuthToken`, the error arm).

### 2.3 The floors and committed prefixes

- **`authFloorD`'s wand is under an update at a mask holding `authTieReadMask`.** This is the fix of `f7-s5-review.md`
  §2.2. With it, the statement is the cross-machine form of the proved `akAuthFixed`.
- **Its content is true of etcd.** Each state the member records at `j ≥ i` is the history's after a committed prefix
  extending `L₀`. This includes a snapshot's state: the leader's at its applied index, later than the floor.
- **Snapshots in the fork.** In the fork, `Recover` and the checks share the locked read (`d52eec43e`). So a check
  interleaving a snapshot apply reads the old state or the new one, both at or after the floor (`watchon-dist.md` (b),
  42,946 probes).
- **R1 still has to be proved.** The retirement obligation R1 (with the alignment lemma) is recorded in
  `KV_GetOn_dist`'s docstring and is not discharged yet. That is expected of an interim axiom and is no soundness
  gap.

### 2.4 A lagging member

- **Writes and linearizable reads are safe without any floor.** Writes are checked at apply, and reads wait on the
  read index (test [lag]).
- **Watch creates need the floor** (above).
- **`New`'s `Authenticate`** at a lagging member also waits (`linearizableReadNotify` first). Its `ErrAuthNotEnabled`
  arm is `enabledVerdict … false`, true of the member's boot state, so it carries no information to misuse.
- **`TimeToLive`.** The check reads the member's own lessor and auth store. The answer's keys come from the leader.
  See §3.
- **Admin calls** proposed at a lagging member with auth off carry the header `""`, which apply refuses once auth is
  on (`adminOk` at the history, `userOk P ""`).

### 2.5 The Serve tie (condition C), with every axiom in the set

- **Every success arm that reads `Γ.au mid` or `Γ.ls mid` is sound only through `Serve_dist`'s tie.** Those arms are
  `readCheckedD`'s `rangeClassFrom`, `authFloorD`, `txnReadCheckedD`, `watchFloorsD`, `New`'s `passwordChecked`, and
  the lease checks. They are sound because `etcdSvc` has no law and `Serve_dist` is its only server. Its auth-on
  premise holds the member's exclusive `authNamesFreshD (Γ.au mid)` (`NewServer_dist`) and the lessor slot at
  `Γ.ls mid`.
- **I checked that no other axiom of the set serves `etcdSvc`.** `PeerServe_dist` serves `httpPeerSvc` only, and
  `grpc.Server.Serve` needs `grpcServes Svc`, which nothing gives for `etcdSvc`.
- **Restarts** are outside it, as its docstring says.

### 2.6 Panics a client can cause on a member (what `Serve_dist`'s "no thread panics" claim rests on)

- **`issues/etcd-auth-snapshot-closed-backend-panic`** (a permission check during a snapshot restore): fixed in the
  fork that is verified and deployed.
- **`issues/etcd-auth-useradd-long-name-fatal`**: excluded by `name.length ≤ maxKeySize` (UserAdd, RoleAdd,
  UserGrantRole's user, RoleGrantPermission's role). It is also an `lg.Fatal`, an exit, not a panic.
- **`issues/etcd-txn-nested-depth-apply-panic`**: excluded by `maxTxnOpsOk` (`NewServer_dist`).
- **`issues/etcd-leasehttp-timetolive-nil-{header,response}-panic`**: need a non-etcd answer at a peer URL. That is
  excluded by `httpAddrAt`'s once-set protocol and `PeerServe_dist` (`NewServer_dist`'s docstring).
- I found no other client-reachable panic in the auth paths of the fork.

## 3. `Lease_TimeToLiveOn_dist` and the TimeToLive disclosure

`issues/etcd-lease-timetolive-keys-toctou.md`: `checkLeaseTimeToLive` checks the keys the **local** lessor holds. The
keys returned come from a second lookup: the leader's after `waitAppliedIndex`, or, on a follower, the leader's
through `leasehttp`. So a key attached after the check, or not yet applied at the follower, is returned unchecked.

The axiom's success arm states:
- `resp.ID ↦□ id`. The server echoes the request's ID, `ID: rr.ID` on `ErrLeaseNotFound`, and the leader's
  `Lookup(r.ID)` otherwise.
- The member's floors `n ≥ n₀`, `j ≥ m₀`.
- `leaseCheckD (Γ.au mid) P n (…)`, whose keys arm is `leaseKeysVerdictFrom … (Γ.ls mid) j id .read`. That is the
  check's own reading of the member's own lessor and auth store, which is exactly what Go checks.

It states nothing about `Keys`, `TTL` or `GrantedTTL`, so a program cannot derive "every returned key is readable by
`P`". **It does not claim past the disclosure.** The docstring's warning ("must keep claiming nothing about `TTL`,
`GrantedTTL` or `Keys`") should stay. The S5 strengthening (`P = some info.Username'`) is right: `requireAuthInfo`,
and `f7-s5-review.md`'s test showed every anonymous or bad-token TimeToLive refused. The axiom is not in
`etcd_safe_nocrash`'s trust base (`etc/tcb-baseline.txt` has no line for it).

## 4. The axiom-tok justifications

**The walk.** `~/eg/logs/f9rev.raw` on fk-lean shows:

- `New_user_dist`:
  - rule 7: `transfer of ∃ P : IProp GF (in a stuck term: Perennial.context.isCancelCtxOf)` ×7, and `transfer of
    ∃ scd : context.ContextDesc (IProp GF) (in a stuck term: Perennial.context.isContextDone, produced: scd.PDone
    ×3)`;
  - rule 5 (the tainted opaques `credsYieldRaw`, `grpcConn`, `grpcConnOptsRaw`, `grpcConnClosedRaw`,
    `builtRawMDRaw`): cascade only, with no roots once the S13/S14 entries are in. The full run is `axiom-tok: ok`;
  - token counts: `tok:L:0` consumed 9, produced 9 in all nine scenarios, so there is no rule-2 finding;
  - verdict `entry`.
- `Serve_dist`: verdict `entry` with its 22 keys, scenario cap (`<capped>`, `Γ.auth = true`), as the entry says.

**J1: `Serve_dist`, section header (lines 189–208) and entry reason (line 209). Corrected text:**

> `etcd_dist.Serve_dist.wp_proof` (Proof/.../examples/etcd/dist/ServeDist.lean; interim, retired by #24's S2)
> consumes the started member's serving resources: with auth off `memberUpL … Γ.kv.lm (Γ.ls mid)`, with auth on
> `memberUpOnL … (Γ.au mid) Γ.kv.lm (Γ.ls mid)` (`dist/MemberLessor.lean`: `memberUp`'s and `memberUpOn`'s server
> handles `isServerReq(M)`/`isServerRead(M)`, the stocks, `srvGoRes`, `srvLeaseRd`, and with auth on `srvAuthLb`); it
> also consumes `etcdAddrAt a Γ mid`, and it returns `True`. Every finding sits inside those consumed persistent
> handles, with the same binders as `leaseTimeToLive`'s and `rangeStream`'s entries:
> - `Dep`/`Rd`/`U`/`Locked` under `isApplyLessor`'s revoke callbacks;
> - `Ψ` under the wait registry's trigger;
> - `Φ : Unit -n> IProp`, an atomic update's fixpoint;
> - `sDoneAny`, `auth.ctxDoneAny`'s;
> - with auth on, `A`/`Pre`/`Y`/`C`/`R`/`Lk`/`Sw` of the auth handles;
> - the rest, those handles' own families.
>
> Unlike those functions, `Serve` does call the handles' methods (it runs the member's request handlers). Why it is
> sound: the post is `True`, and every finding is inside handles the axiom only consumes. Only etcd's proved start
> builds them (`memberUpL` through `etcdstart.wp_Start_builtL`, `memberUpOnL` from `memberUpOn_intro`'s parts; the
> server's fields are unexported), so no user-written callback ever runs. The keys come from the handles' definitions
> themselves (the same keys appear for `leaseTimeToLive`, which never calls them). The proved in-process analogue is
> `etcdstart.Serve.wp_proof`, over `memberUp` (auth off) and over `memberUpOn` through `memberUpOn_served` (auth on).
> It is not literally the same predicates: the `L` variants add the lessor name, and `Serve.spec` takes `netAddrFree`
> and a view-shift that `Serve_dist` replaces. The walk hits the scenario cap, so its rule-3 counts are merged ones.
> `7:P:IPropGF` is not among `leaseTimeToLive`'s keys; most likely it is the per-request context the gRPC server picks
> for the handlers (harmless: those contracts are generic in it); not traced.

The entry line's reason should read "… the handles' contracts are discharged by the proved in-process
`etcdstart.Serve.wp_proof` over the corresponding in-process handles (`memberUp`; `memberUpOn` via
`memberUpOn_served`), and the post is `True`", in place of "over the same handles". Its keys are unchanged.

**J2: `New_user_dist` (line 364). Corrected text:**

> `New`'s shape (notes/axiom-review/f7-auth-axiom-tok.md; re-walked in f9-auth-combined-review.md §4). `P` is the Done
> proposition of the `*cancelCtx`s inside the client handle the post returns (`isNewClient`; there it is produced, in
> `KV_Put_dist`'s pre consumed). `scd` is the `∃ scd` of that handle's lessor (`lessorAt`: its `stopCtx`'s
> description, `context.isContext sc scd`, under `isContextDone`, whose `scd.PDone` the walk counts as produced): rule
> 7's neutral case through a defined handle, as NewStream's `cd'`. The caller's `levelTok 0` is taken and returned
> (the walk: `L:0` consumed 9, produced 9 in every scenario; no rule-2 finding). There is no auth-off sibling: no
> auth-off `New` axiom exists, because the auth-off clients come from the proved `New`.

The exact source of `P` inside `isNewClient` is not traced. The client's own `ctx` and the watcher's contexts are the
likely ones. The S3 note's guess, "the context `getToken` makes inside the call", does not match the walk for `scd`.

**S13/S14 blocks.** The keys and counts agree with the walks. Two remarks:
- The S13 header's "Watch's 8/0" is right: `WatchOn_dist`'s entry `2:L:0:handedtoacallback8/supplieddirectly0`.
- Both blocks end "For the lead's confirmation". This review is evidence for it.

## 5. Docstring fixes (statements unchanged)

- **D1** (`watchon-dist.md` F5, never applied). In `Proof/.../dist/ServeDist.lean`, replace "the watch streams of
  `Watch_dist`/`RequestProgress_dist`" with "the watch streams of `Watch_dist`/`RequestProgress_dist`/`WatchOn_dist`
  (with auth on, the stream carries the client's own token or none, and metadata meeting `outTokOkS`; the handler's
  refusal path is `isWatchPermitted`'s, proved in process)". `WatchOn_dist` has been in the trust base since S13, so
  this deferral has expired.
- **D2** (`watchon-dist.md` F4, never applied). In `Proof/.../dist/WatchDist.lean`, `Watch_dist.wp_proof`'s bullet
  "*Any auth mode.*" still says "with `Γ.auth = true` no member serves `Γ`", which has been false since F7 step 3.
  Replace it with `watchon-dist.md` §7's text: "*Any auth mode.* With auth off (`memberUpL`) no create is refused.
  With auth on (`Serve_dist`'s `memberUpOnL` since F7 step 3), a refused create (permission denied, empty user,
  invalid token, old revision) is a created-and-canceled response with its reason, the error arm. A passing create's
  events are the cluster's, as with auth off. No row is claimed: `WatchOn_dist` states it."
- **D3.** In `Spec/.../dist/TxnCommitOnDist.lean`, the last sentence "Unchanged since (`f7-changed-since-review.md`)"
  is stale (S5 lease widening, S11 nesting). Replace it with "Widened since (S5, S11); reviewed `f7-txn-review.md`,
  `f7-txn-nested-review.md`, and with the set `f9-auth-combined-review.md`." The "needs a fresh review" notes in
  `KV_GetOn_dist`, `Txn_CommitOn_dist` and `Lease_TimeToLiveOn_dist` (the S5 strengthenings) can cite this review.
- **D4.** In `Proof/.../dist/ServeDist.lean`, "each of which carries the calls of the clientv3 contracts
  (`KV_Put_dist`, …, `Txn_Commit_dist`)" names only the auth-off contracts. Add the auth-on ones it now serves:
  `KV_PutOn_dist`, `KV_DeleteOn_dist`, `KV_GetOn_dist`, `Txn_CommitOn_dist`, `New_user_dist`'s `Authenticate`, the
  five `Auth_*_dist` admin calls, and the `Lease_*On_dist`/F2 lease calls. With auth on, the handlers are the
  `etcd*SpecOn` ones at `T := False`, as the spec's docstring already says.

## 6. What was not tried

- No Lean counterexample: no Go behavior violated a premise-satisfying post.
- I tested no crash or restart: every axiom here is no-crash only (`Serve_dist`).
- JWT tokens and client-certificate auth are not in the deployment.
- I did not exercise an `AuthDisable`. No cross-machine axiom covers it (only the server-side and in-process specs
  `EtcdServer__AuthDisable`, `AuthServer__AuthDisable` exist), so a program over these axioms cannot send one. `New`'s
  `enabledVerdict … false` arm and the grant model both allow disabled states anyway.
- I found no issue in the verified Go code that is not already in `issues/`.
