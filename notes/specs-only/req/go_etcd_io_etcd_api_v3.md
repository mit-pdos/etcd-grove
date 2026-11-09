# Requirements on the client-observable model and state (`Spec/go_etcd_io/etcd/api/v3/`, batch W0)

## from 1f

1. **The current revision with one to spare**: `etcdState_revFits` gives `σ.kv.rev < 2^63`; the
   recipes compute `resp.Header.Revision + 1` in `int64` (`Barrier.Wait`'s watch start,
   `newSequentialKV`'s guard), which wraps at `2^63 - 1`. Wanted: `σ.kv.rev + 1 < 2^63` (the
   adequacy theorem's step bound gives any margin).
   ```go
   _, err = WaitEvents(b.client, b.key, resp.Header.Revision+1, []mvccpb.Event_EventType{mvccpb.Event_DELETE})
   ```
   Used by: `Barrier.Wait.spec`, `newSequentialKV.spec` (their sketches).

2. **The cluster's states are well formed**: a law giving that every state the cluster has been in
   is reachable from an initial one (`etcdLb γ σ ⊢ ⌜∃ ms, Reach (State.init ms) σ⌝`), or the
   facts it implies stated as one well-formedness predicate: a present key has version `≥ 1` and
   create revision `≤` mod revision `≤ rev`, and its mod revision is the revision of the event that
   wrote its record. Without it a recipe that reads `σ0` cannot conclude that `Version(k) = 0`
   means `k` is absent (`putNewReq`: the created record is a first version, `createdAt`), nor that
   a key present at a later state with a mod revision `≤ σ0.kv.rev` was present at `σ0`
   (`frontByRev`, `frontByKey`: the queues' front at the claim).
   Used by: `Queue.Dequeue.spec`, `PriorityQueue.Dequeue.spec`, `DoubleBarrier.Enter.spec`
   (`createdAt`), `RWMutex.Lock`/`RLock.spec` (the key's revision).
   (The same holds of 1d's `Mutex` sketches: a client proving a pure fact of the model from an
   `etcdLb` needs the state's provenance.)

## from 1b

1. **The watch messages belong with the KV ones** (`Wire.lean`): 1b defined, in
   `Spec/go_etcd_io/etcd/client/v3/ApiWatch.lean`, the models `EventM` (`mvccpb.Event`),
   `WireWatchRespM` (`pb.WatchResponse`), `WireWatchReq` (`pb.WatchRequest`'s create, cancel and
   progress), with `eventOwn` (and `eventOwn_unfold`), `wireWatchRespOwn`, `watchReqOwn`; 2b builds
   them, so they would be better in `api/v3/Wire.lean` (or a `WireWatch.lean` next to it). If W0
   moves them, 1b's files only change their import. 1b did not edit W0's files.
2. **A compaction retention in the environment's configuration** (`EnvCfg`): `examples/etcd/
   compactwatch/compactkv.go:142` panics unless `Get.rev ≥ CompactRevision + retention`; the
   watch's compaction fact (`CompactRevision ≤ σ.kv.compacted`) gives the bound only if the model's
   auto-compaction step keeps `compacted ≤ rev - retention` (`EnvStep.compact`'s `r ≤ σ.kv.rev`
   allows any). Not needed by any other watch user; a question for W0's model (and the user).
3. **A pure fact clients need, theirs to prove** (no request, noted for the reviewers): `Reach σ σ'`
   keeps the history a prefix (`σ.kv.revs <+: σ'.kv.revs`) and the compaction revision monotone;
   every watch consumer reads `watchStep`'s facts at `σ` against its own later state through it.

## from 1d

1. **The cluster's states are well formed** (the same request as 1f's item 2): `etcdLb_init :
   etcdLb γ σ ⊢ ⌜∃ ms, Reach (State.init ms) σ⌝`. 1d's sketches use it for: a present key has a
   create revision `≥ 2` and a mod revision `≥ 2` (so `CreateRevision(k) = 0` and
   `ModRevision(k) = 0` mean `k` is absent: the mutex's and election's create-if-absent
   transaction, the STM's `isKeyCurrent` of an absent key); `Mutex.Lock`'s `myRev - 1 > 0`
   (`waitDeletes`' filter is off at `0`).
   ```go
   cmp := v3.Compare(v3.CreateRevision(m.myKey), "=", 0)
   werr := waitDeletes(ctx, client, m.pfx, m.myRev-1)
   ```
   Used by: `Mutex.tryAcquire.spec`, `Mutex.Lock.spec`, `Election.Campaign.spec`,
   `stm.commit.spec`, `stmSerializable.commit.spec`.

## from 1g

1. **The read permission `etcdPeek γ`** (1f's definition, `client/v3/experimental/recipes/Api.lean`):
   the cache defines the same body (`Cache.etcdPeek`) for `New`'s precondition (its background list
   and the revision a linearizable `Get` waits for are client `Get`s that need a persistent update).
   Wanted: one definition in `State.lean`, which both batches then cite.
   ```go
   resp, err := c.kv.Get(ctx, c.prefix, clientv3.WithPrefix())   // the cache's own read
   ```
   Used by: `New.spec`, `Cache.get.spec`, `Cache.serverRevision.spec`.
2. **Revisions only grow** (`Reach σ σ' → σ.kv.rev ≤ σ'.kv.rev`, a pure lemma the cache proves
   itself; noted, no request): `Cache.serverRevision.spec`'s `σ0.kv.rev ≤ σ1.kv.rev`.
4. (1b, round 1) **A bound law on reached states**: `etcdLb γ σ ⊢ ⌜σ.kv.rev < 2^63 ∧
   σ.kv.compacted ≤ σ.kv.rev⌝`, so that a watch consumer without the owner's invariant (Kubernetes'
   watcher) can compare revisions it reads (`etcdState_revFits` gives it only at the current state).
   (Update: W0's round 2 added `etcdLb_revFits`; the `compacted ≤ rev` half follows from the
   model, a pure lemma of the client.)

3. (1f, round 1) **A transaction puts a key at most once** (etcd's `checkIntervals`; a put then a
   delete in sibling nested transactions excepted). Without it a watch may deliver a put of `k` at
   revision `m` whose value is not the record `k` holds at `m`, and `Queue.Dequeue`'s value on its
   watch path is unprovable (review 1f-provability-1, F2). Done by W0's round 2: `kvStep`'s
   `putOnce evs`, which `Queue.Dequeue.spec` and `PriorityQueue.Dequeue.spec` cite.

## from 2c

What the server's request path (2c, `Spec/go_etcd_io/etcd/server/v3/etcdserver/ApiReq.lean`) found of
W0's model, against the code:

1. **`leaseKeepAlive` lacks a permission refusal.** `LeaseRenew` runs `checkLeaseRenew`
   (`v3_server.go:574`): with auth enabled, a principal without put permission on one of the lease's
   keys gets `ErrPermissionDenied` (and no principal `ErrUserEmpty`, a refusal). `leaseStep`'s
   `leaseKeepAlive` allows only `ErrLeaseNotFound` and a TTL. Add `res = .err (AuthState.permErr
   who)` (as `leaseTimeToLive` has). Until then 2c's `srvStep` carries that disjunct.
2. **`Authenticate`'s update must be persistent.** The server checks the password at the member's
   applied auth state, proposes the token, and retries while the auth revision changed
   (`v3_server.go:852-886`): the answer rests on a state the member read, which the cluster may have
   left before the call returns; only the read registry (fired at every state after the call began)
   can fire it there. The client passes a one-shot update (`CallTriple`'s `□?(reqRetryRep rq)`, false
   for `.authenticate`). Since `authenticate`'s step changes nothing (`σ' = σ`), ask for a persistent
   one without making the client resend it: `□?(reqRetryRep rq || rq.isAuthenticate)` in the update,
   `reqRetryRep` alone in the retry policy. Used by: `EtcdServer.Authenticate.spec`.
3. **The `doSerialize` race** (`nonissues/etcd-doserialize-auth-enable-race.md`, K8's open
   question): 2c states what the code does, `srvStep`'s race disjunct (a linearizable read whose
   permission check ran with auth disabled answered at a state where auth is enabled, by the step at
   that state with auth off). The client's `Step`-only contract holds once the user decides: a fix on
   the fork (re-check the permission after the read when auth is enabled by then) removes the
   disjunct; a scope premise (no `AuthEnable` while reads are in flight) makes it unreachable.

## from 2a

What batch 2a found of the model and of W0's boundary requirements against the code (rpctypes,
v3rpc, grpc-go v1.84):

1. **`kvStep`'s `.compact` lacks the admin refusal.** `kvServer.Compact` (`key.go:144`) checks
   `aa.isPermitted(ctx)` first: with auth on, a principal without the root role is refused with
   `ErrPermissionDenied` (or `ErrUserNotFound`, `ErrUserEmpty`), at the member's local auth state,
   before proposing. The model's compact step has no such answer (`.permissionDenied` and
   `.userNotFound` are not refusals). Needed: a disjunct `σ' = σ ∧ res = .err (σ.auth.adminErr who)`
   at any state, as `clusterStep` has for the member and alarm requests. Used by: `kvServer.Compact.spec`,
   the snippet `examples/specreq/v3rpc/kv.go`'s `ReqCompactAdmin`.
2. **Six `EtcdErr`s are not mapped by `rpctypes.Error`** (`errStringToError` has no key for their
   description): `.timeoutWaitAppliedIndex`, `.canceled`, `.deadlineExceeded`,
   `.invalidClientAPIVersion`, `.watchCanceled`, `.permissionNotGiven`. A status with one of their
   descriptions stays a status through `rpctypes.Error` and `ContextError`: the client returns it, not
   `errVal e`. So: (a) W0's header statement that `ErrGRPCCanceled`/`ErrGRPCDeadlineExceeded` are
   `.etcd` of the indefinite kinds is false: they are `.other` (`Rpctypes.callErr_view`: `.etcd e`
   only for a mapped `e` or the value `errVal e`), harmless (both indefinite); (b)
   `ansReply`/`putReply`'s `err = errVal e` for an answer `.err e` is false at
   `.permissionNotGiven` (a `RoleGrantPermission` answer) and `.invalidClientAPIVersion` (a refusal):
   the client returns the status. 2a's contract therefore sends those answers as "unsettled"
   (`V3rpc.indefMsg`), which W0's specs admit; a model where they are never `Step` answers (or the
   rpctypes map fixed on the fork) would make them definite. (c) `rpctypes.ErrTimeoutWaitAppliedIndex`
   holds the status error, not `errVal .timeoutWaitAppliedIndex` (`Rpctypes.init.spec`).
3. **`CallErr.notSent` never occurs**: grpc-go v1.84 has no error with the messages "there is no
   address available" / "there is no connection available" (`client/retry.go:93` tests for an old
   grpc's). No error of grpc's is `.notSent` (`Grpc.ownErr` is `.other`: `Rpctypes.callErr_ownErr`), so
   the retry interceptor resends a mutable RPC only after a token or learner refusal. Sound as W0
   states it; the case is dead.
4. **Oversized messages panic in grpc-go** (W0's item 3 of `req/google_golang_org_grpc.md`): a
   message whose encoding exceeds `2 ^ 48` bytes panics in the codec's allocation, on the client
   (sending) and the server (replying), `issues/grpc-codec-alloc-before-size-check.md`; below that,
   limits are `ResourceExhausted` errors. So "an error rather than a panic" is **false of grpc-go**.
   2a states the boundary under a **workload premise** `Grpc.msgsFit` (every message the program's
   gRPC clients and servers marshal fits: `Proto.Content.fits`, which also bounds the nesting depth),
   taken where a connection or a server is made (`Grpc.NewClient.spec`, `Grpc.start.spec`), not by any
   call: W0's client specs keep no size premise, and the closed theorems are conditional on it (a
   decision for the user, `notes/specs-only/batch-2a.md`).
5. **`servesAt` realized** (`V3rpc.servesAt_addr`): `servesAt γ ep ⊣⊢ Grpc.addrAt ep (etcdContract γ)`,
   the address bound for good to etcd's contracts (so a member restarted at the same address serves
   the same contracts). Binding an address takes `Grpc.addrFree ep`, a resource of the program's
   environment given by the adequacy theorem, one per address (decision for the user).
6. **At most once** (W0's item 1): true of grpc-go as `Grpc.attemptOk_call` states (one run per
   attempt; transparent retries only of streams that never reached a handler; no retry policy: the
   client's service config sets only the balancer, and `Grpc.dialOptAt`'s options cannot set one).

## from 2e

On the cluster contract (`top.md`, K1-K2), as 2e stated it (`ApiBoot.lean`):
1. **K1**: `cluster_alloc` gives `etcdState γ (State.init ms)`, one `memberBoot γ ms m` per member, and
   `memberUrls γ (peer URL sets)`. The members `ms` are `Membership.initialMembers token cluster` up to
   order: their ids are SHA-1 values (`memberIdOf`, opaque) a program learns by running Go; no premise
   on them (duplicate or zero ids make `bootstrap` fail).
2. **K2's join** is keyed by the peer URLs (`memberJoin γ urls`, from `memberUrls_take`), not by an
   `etcdLb` naming the member: `bootstrap` runs a joiner as whatever id the cluster has for its URLs
   at that time (an id-keyed token would let two processes run one id). `NewServer`'s post names the
   member id existentially.
3. **K6, restarts**: after `HardStop`/`Stop` only (`memberDisk`); a restart after a crash is not in
   2e's specs (no crash rule: open question Q2 of `batch-2e.md`).
4. Metrics: 2e uses a provisional `EtcdServer.gaugeVecOk gv` (`addFeatureGateMetrics`); W0 owns the
   metrics boundary.

## from W0 (round 4): to 2c, the names of the read window and the principal

`Step who rq σ σ' res lo` (optional `lo`, the auth state's index at the call's start): a linearizable
read's permission is checked at `σ`, or the check saw auth off since `lo`
(`State.authOffSince`), and a denial is at an auth state since `lo` (`State.deniedSince`), over the
new `State.authHist`/`State.authTables`. 2c's read path fires the client's persistent update with
`lo` the auth history's length at the read's registration (minus one). The principal: `who` is the
server's principal with auth on (the token's user, else the certificate's CN); with auth off no
check depends on it. `Authenticate` answers `.ok .authenticate` (no token); the token is
`tokenUser γ tok u`, a persistent fact 2c/3d give with the reply. Compact's admin check and
keep-alive's permission error are at any auth state the cluster has had.

## from 3c

1. **`leaseTimeToLive`'s keys** (`Model.lean`, `leaseStep`): the answer's keys are "exactly those
   attached at some revision `r`". etcd's leader reads the lease object's key set while the apply
   thread may be between two `Detach`es of a revocation's deletes or two `Attach`es of a
   transaction's puts (`nonissues/etcd-lease-keys-mid-apply.md`): a set no revision had. Each key's
   membership changes at most once in an entry (a transaction writes a key once), so the step that
   is true of etcd: for some `r < σ.kv.rev` (or `r = σ.kv.rev`), the keys lie between
   `attached(r) ∩ attached(r + 1)` and `attached(r) ∪ attached(r + 1)` (the revisions of one entry's
   writes). Needed by 2c's `leaseTimeToLive.spec` over `Lease.Keys.spec`.
2. **No time model is needed by the lessor's callers**: the remaining TTL (`Remaining()`), the
   checkpoints, the primary flag and the expiry are not modelled; `TimeToLive`'s `TTL` is any value
   and `KeepAlive`'s any TTL (as W0 has them). `EnvCfg.leaseExpiry = false`'s premise is the
   lessor's opaque `Lease.leasesOutliveRun` (taken at `NewLessor`).
3. **A member's granted TTL** is `max ttl minTTL` of that member's lessor (`Lease.grantTTL`): W0's
   one `LeaseRec.ttl` per lease cannot be every member's; W0's `leaseTimeToLive` already allows any
   positive granted TTL, so nothing to change unless a client needs the TTL.

## from 2a, round 1

- The read handlers compose with 2c only when a read's permission is checked at an auth state
  reached between the call's start and its answer (the coordinator's decision, W0's round 4).
  2a's specs assume that 2c's `srvStep` is then `Step`.
- The compaction (`kvStep`'s `.compact`) needs the admin check on both sides: a refusal answer
  `adminErr` at a state the call saw, and **success only for an administrator at a state the call
  saw**. This makes `examples/specreq/v3rpc/kv.go`'s `ReqCompactAdmin` provable. The member's check
  is local and the apply does not repeat it (`nonissues/etcd-compact-admin-check-lagging-member.md`).
- The contract is per member: `servesAt γ ep ⊣⊢ Grpc.addrAt ep (V3rpc.etcdContract γ ep)`. The lease
  requests carry and give `leaseViewLb γ ep` (`V3rpc.leaseFact`).
- A definite error's gRPC code is `Rpctypes.code e`, or `Unknown` for `.tooManyRequests` and
  `.memberNotEnoughStarted` (`Rpctypes.callErr_view`, `code_not_ctx`).

## from 3b

(Round 1, the review's F1: the earlier request, that an empty range end be the `nil` slice, is
**withdrawn**: `clientv3.WithRange("")` builds a non-`nil` empty end, and an embedded server's
`v3client` passes it to the server.) Needed instead: **the request predicates read the end slice as
mvcc does**: in `rangeReqOwn`, `deleteReqOwn`, `compareOwn` (and so `txnReqOwn`'s operations), a
`nil` end slice is the model's `[]` (the key alone) and a non-`nil` empty one is `[0#8]` ("every key
from the key on", what `mkGteRange` makes of `"\x00"` and mvcc's index reads an empty end as), any
other end its bytes. Then W0's `KeyRange.mem` is mvcc's `MRange.mem` of the slice actually passed, and
txn's `Range`, `DeleteRange`, `Txn` (through `applyCompare`, `executeRange`, `deleteRange`, `txnSafe`)
need no premise. Used by: those specs; `Count.spec` reads its raw slice the same way (`Txn.endOf`).

## from 3a

What the apply layer (3a: `Spec/go_etcd_io/etcd/server/v3/etcdserver/apply/Api.lean`) needs of the
model, to state the apply of every entry as a `Step` (`irrStep_step`) or an `EnvStep`
(`irrStep_env`):

1. **`ErrNoSpace` does not settle a request** (`EtcdErr.indefinite .noSpace = true`, keeping it a
   refusal too): the quota applier applies a put, a write transaction or a grant and answers
   `ErrNoSpace` when the member's backend is over its quota (`quota.go`;
   `nonissues/etcd-apply-quota-nospace-after-write.md`). The history moves by the write; the
   proposer's reply is `ErrNoSpace` (3a's `resMatch`), which 2c can only return as outcome 3 if it
   is indefinite.
   ```go
   ok := a.q.Available(p); resp, trace, err := a.applierV3.Put(p)
   if err == nil && !ok { err = errors.ErrNoSpace }            // quota.go:36-43
   ```
2. **The stored credential, not the password**: the request path hashes the password before
   proposing (`v3_server.go`, `UserAdd`/`UserChangePassword`: `HashedPassword`, `Password` cleared);
   the apply stores the hash and never sees the password, so a state that stores `some pw` is not a
   function of the log. Needed: `UserRec.password` the stored credential, `authenticate` succeeding
   iff a trusted `pwMatch cred pw` (bcrypt's `CompareHashAndPassword`, 3d's boundary), and `Step`'s
   `userAdd name pw` storing some `cred` with `pwHash pw cred`. 3a's `opStep_userAdd` states the
   apply as `authStep` with the hash in the password's place.
3. **No user with the empty name** in reachable states (an `etcdLb` law: `UserAdd` refuses `""`):
   the apply's `RoleGet` check for a request with no user asks `HasRole("", r)`; 3a's `irrStep_step`
   takes it as a premise.
4. **A grant's TTL** is the asked one raised to the member's minimum (`lessor.Grant`): `leaseStep`
   allows any `ttl' ≥ ttl` (fine); a member's state differs from the proposer's in the TTLs only
   (3a's `ttlEq`, `irrStep_ttl`). No change needed unless the user wants the members alike (a
   decision: `notes/specs-only/batch-3a.md`).
Used by: `irrStep_step.spec`, `opStep_userAdd.spec`, `resMatch` (3a's `Api.lean`).

## from 2c (round 1)

1. **The doSerialize race and the keep-alive denial**: 2c's `srvStep` now relies on W0's round-4
   `Step` (a read's permission at an auth table since `lo`; `leaseKeepAlive`'s `permErr`): no
   disjuncts of its own.
2. **`Authenticate`**: 2c takes a one-shot update (round 1). The token entry's commit fires it with
   `.ok .authenticate` when the auth revision is the checked one; the apply's `ErrAuthNotEnabled` and
   `ErrAuthFailed` are fired at the commit too. But `CheckPassword`'s own errors (`ErrAuthNotEnabled`,
   `ErrAuthFailed`, `v3_server.go:853-862`) are returned before anything is proposed, decided at the
   member's applied auth state `kp`, which the cluster may have left: **`authStep`'s `authenticate`
   should admit those two answers from an auth table at or after `lo`** (as the reads' `deniedSince` /
   `authOffSince`), so the update can be fired at the return.
3. **The principal pair** (`nonissues/etcd-write-tls-principal-auth-enable.md`): with a token of `A`
   and a TLS certificate of `B` (`--client-cert-auth`), a write proposed while auth is disabled and
   applied after `AuthEnable` is checked as `B`. 2c's specs say so (`srvStep p tls`: `Step tls` for a
   write). `ctxPrin`'s header says "a context carrying both a token and a certificate is covered by
   the token's user": not for this write. Either a premise of `ctxPrin` (the certificate's name, if
   any, is the token's user) or a refusal-only argument (`tls = none`: a principal-less write is
   refused with auth on).
4. **`leaseTimeToLive`'s keys**: the lessor's `le.Keys()` may see a write transaction's attachments
   half done (`storeTxnWrite.put`/`delete` attach or detach one key at a time while the apply runs,
   `mvcc/kvstore_txn.go:273,285,338`): a key set no revision had, which `leaseTimeToLive`'s
   `∃ r, … storeAt r …` excludes. A model mismatch (provability F4): admit any key set between two
   revisions' or record a non-issue.

## from 3d

What the auth store's specs (`Spec/go_etcd_io/etcd/server/v3/auth/`) found about W0's auth model,
checked against `server/auth/store.go` (W0's item 2 asked for it):

1. **`authenticate`'s success must not claim the password is the user's.** bcrypt reads only the
   first 72 bytes of a password (`nonissues/etcd-auth-password-72-byte-prefix.md`: a user with a
   72-byte password authenticates with any extension of it) and hashes collide; the boundary
   (`Spec/golang_org/x/crypto/bcrypt/`) assumes only that a hash accepts its own password. Needed:
   `authStep .authenticate`'s success allowed whenever the user exists with a password (`∃ ur p,
   a.users name = some ur ∧ ur.password = some p`), the failure (`authFailed`) only when the user is
   absent, password-less, or `p ≠ pw`. Used by: `authStore.CheckPassword.spec` (its success names no
   password), 2c's `Authenticate.spec`.
2. **`tokenUser_agree`**: `tokenUser γ tok u ∗ tokenUser γ tok u' ⊢ ⌜u = u'⌝` (a token names one
   user): what lets the request path conclude that `AuthInfoFromCtx`'s user (`tokenUser γ tok u`) is
   the client's (`ctxPrin`, 2a's `mdPrin`). And `tokenUser`'s meaning must include the tokens a member
   issues itself: `WithRoot`'s root tokens (`prefix.0`, index `0`, never an entry's) and the JWTs the
   members' keys sign (`Auth.jwtTokOk`). Used by: `examples/specreq/auth/token.go` (`ReqTokenUser`,
   `ReqWithRoot`).
3. **`roleGrantPermission` with an invalid range**: the model's success case admits any `perm`; the
   store refuses an empty key, or a range end that is neither empty, `"\x00"` nor above the key
   (`isValidPermissionRange`: `ErrInvalidAuthMgmt`). Needed: the success case only for a valid range
   (`Auth.validPerms`'s condition), so that every reached state has valid permissions (a fact clients
   prove from `Reach`) and `Recover`/`NewAuthStore`'s premise `validPerms a'` follows from
   reachability.
4. **An inverted range** (a proper `rangeEnd` at or below the key): `AuthState.covers` holds of it
   vacuously (no key is in it), so `State.permits` passes, but the store's interval tree may refuse
   it (`Contains` of an empty interval): a read or delete of an inverted range by a user without
   permissions on it is answered `ErrPermissionDenied` where the model requires `¬ permits`. Needed:
   the model's check left open for inverted ranges (a denial allowed), or `covers` defined as the
   tree computes it. (`Auth.rngInverted`; `checkPost`'s denial carries the disjunct.)
5. **A request with both a token and a client certificate** of different users, across an
   `AuthEnable`: with auth off at the proposer, `EtcdServer.AuthInfoFromCtx` falls back to the
   certificate's user (the store returns no credentials when auth is off) and the header carries that
   user at the current revision, which `AuthEnable` does not bump; if the apply finds auth on, the
   check is the certificate user's, not the token's. The principal (`ctxPrin`) should exclude this
   case (a scope premise: one identity per client) or it goes with
   `nonissues/etcd-doserialize-auth-enable-race.md`'s decision.
6. **`roleGet "root"` with no stored role `root`**: the model answers a list whatever is stored
   (`name = rootRole ∧ ∃ ps, res = .ok (.roleGet ps)`), but the store returns `ErrRoleNotFound` when
   no role named `root` is stored (`auth/store.go`, `RoleGet`: `as.be.GetRole` first, `rootPerm` only
   for a stored `root`); the usual setup (`user add root`, `user grant-role root root`) stores none,
   since `UserGrantRole` does not require the root role to exist. Needed: `roleGet rootRole` answers
   `roleNotFound` when `a.roles rootRole = none`, a list otherwise. **Until then
   `authStore.RoleGet.spec` is false at that input** (it claims W0's `authStep`).
7. Confirmed against the code, unchanged: `userAdd`, `userDelete` (`root` with auth on refused),
   `userChangePassword` (a password-less user stays so), `userGrantRole` (a duplicate changes
   nothing), `userRevokeRole`, `roleAdd`, `roleDelete` (the role removed from every user),
   `roleRevokePermission`, `roleGet` (`root`: any list), the lists, `authEnable` (keeps the revision),
   `authDisable` (bumps), `mayCall`'s self cases (`authApplierV3.UserGet`/`RoleGet`).

## from 2e, round 1

1. **The auto-compactor's lag** (2e's completeness F6: `examples/etcd/compactwatch`'s check C3,
   "every compaction is at least the retention behind a revision the cluster reached"). `EnvCfg`
   should carry the compactor's lag (`compactLag : Nat`, `0` for periodic mode or none) and
   `EnvStep.compact` require `r + lag ≤ σ.kv.rev`. 2e's `V3compactor.bootCfg` then ties the revision
   mode's retention to it (`bootCfg_on` at `lag ≤ ret`) and the server's `Compactable` commits only
   such compactions (the revision compactor compacts at `rg.Rev() - retention`).
2. **K6 / item 5 say "graceful stop only"** until raft's crash transition exists (`req/go_etcd_io_raft_v3.md`,
   "from 2e, round 1"): a restart after `HardStop`/`Stop` loses no answered step; after a crash, no
   spec says so yet.
3. **The adequacy statement's program-start resources**: `EtcdServer.dataDirFresh ds` per data/WAL
   directory pair (canonical, pairwise distinct paths), `Http.addrFree a` per peer host (2f), and
   `EtcdServer.backendEnvOk` (`ETCD_VERIFY` unset for the run).
4. K2's join is by a single-use peer-URL set (`urls_reserve`: `urlsRight`, `memberJoin`), not by an
   `etcdLb` naming the member: the program's `MemberAdd`/`MemberUpdate` calls take `urlsRight`
   (round 1, provability F4).
5. Alarms (second tier F13): a client `AlarmActivate` of an unknown type reaches the alarm store with
   its raw type (`apply/backend.go:116-131`); the model has no client activation; say what it is.

## from 2e, round 2 (crash restart)

1. **The adequacy theorem's crash rule** gives `EtcdServer.crashGone γ ds` for each disk whose
   server was running at the crash (with raft's `nodeVacant`, as R1's `raftState_crash` assumes), and
   keeps the program's crash invariant holding `EtcdServer.diskState γ ds k`. With 2e's `disk_crash`
   (under `crashScope`), K6's "a restart loses no answered step" holds after crashes too.
2. **`crashScope`** is an environment premise of that crash rule (the user's decision): R1's
   `Durable.confAboveOk` at the crash, and no crash during a snapshot-carrying write.

## from 3c (round 1)

1. **The restore window** (adds to "from 3c" item 1): after a snapshot's `Recover`, mvcc's `Restore`
   re-attaches the snapshot's keys one at a time, so a leader's `TimeToLive` with keys may answer any
   subset of the keys attached at the snapshot's revision (`Demoted()` does not always catch it: a
   `Renew` refreshes a loaded object). The relaxation should admit it too
   (`nonissues/etcd-lease-keys-mid-apply.md`).


## from 3a (round 1)

5. **An inverted range** (`Auth.rngInverted`: a proper `rangeEnd` at or below a non-empty key) is
   refused by etcd's permission cache for a non-root user (`ErrPermissionDenied`), while
   `AuthState.covers` holds of it vacuously, so `State.permits` grants it. 3a's `irrStep_step`
   excludes such requests (`checksSane`) until the model agrees (e.g. `covers` false of an
   inverted range, or `permits` refusing it).
6. 3a's refinement laws take `reachable σ` (`∃ ms, Reach (State.init ms) σ`, which `etcdLb_init`
   gives): lease `0` never live, every key's lease live, no user `""` are pure consequences; laws
   stating them (or 3a proves them) close `irrStep_step`.

## from 3d, round 1

Rounds 5 and 6 answer items 1-4 and 6 of "from 3d" (`pwHash`/`pwMatch`, `tokenUser_agree`,
`validPerm`, `invertedDeny`, `roleGet "root"`, `permittedSince`); 3d's specs now use them. Open:
- **`roleGrantPermission` with a nil or unknown-typed `Perm`** (review S4): a client's request reaches
  the store unchanged (`ErrPermissionNotGiven`; an unknown type is stored and ignored by the checks);
  `Req.roleGrantPermission name perm` cannot express it, so 3a cannot apply the store's spec to it.
  Needed: an `Option Perm` (or a raw type) with the deterministic errors.
- **Answer orders** (review S5): the store answers `UserList`/`RoleList` in key order, `UserGet`'s
  roles sorted, `RoleGet`'s permissions sorted by key (unstable). W0's lists are "any permutation"
  (fine for 3d); if 2d/3a need the apply's answer equal to the committed one, the model must fix an
  order.
