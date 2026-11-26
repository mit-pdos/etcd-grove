# Review: `etcd_dist.authd.WatchOn_dist.wp_proof` (auth-on cross-machine watch, the auth row)

2026-11-26, `axiom` skill, a fresh review, read-only on the repository. Branch `etcd-safe-watchon/2026-11-26` at
`6ad10329bc`. Go: the etcd fork at `df6af0c36a6b` (module cache), grpc-go v1.84.0, go1.27.3.

**No etcd disclosure or permission hole found.** On a 3-member auth-on cluster, no principal got events of a
range it may not read, except through the two routes the statement's premises already exclude (an issued token in
the context's metadata, and a stream shared with such a context). The lagging-member behaviour below is etcd's
design (the create is checked against the receiving member's own state, and only at create time). The
deployment's per-member barriers exclude it.

## Verdict

**SOUND WITH FIXES. The statement is unchanged. The fixes are docstring fixes only (F1–F5).** No program built
from these premises gets events on a watch that the real Go refuses. I found no premise that is unsatisfiable,
and none that is mintable in a way that matters.

| # | severity | finding | fix |
|---|---|---|---|
| F1 | low (doc) | `outTokOkS`'s docstring example of a stream-key collision is wrong: `fmt` sorts map keys | replace the example (below) |
| F2 | medium (doc, trust argument) | "The state" bullet says "as in one process". But a snapshot apply (`authStore.Recover`) never happens in a one-member process, so its interleaving is new trust that the in-process proof does not cover | add the Recover argument (below) |
| F3 | low (doc) | the per-member floor is load-bearing (Go test [lag]), and the docstring does not say so | one sentence (below) |
| F4 | low (doc, sibling) | `Watch_dist`'s "Any auth mode" bullet is stale since F7 step 3 ("with `Γ.auth = true` no member serves Γ") | restate (below) |
| F5 | low (doc, interaction) | `Serve_dist`'s docstring lists the watch streams of `Watch_dist`/`RequestProgress_dist`, not `WatchOn_dist`'s auth-on streams | add `WatchOn_dist` (below) |
| — | info | trigger (4) of `WatchDist.lean` (a new axiom locking `w.mu`): reviewed, the encapsulation still holds | update the audit row's trigger text |

## 1. The claim, read from the code

`WatchOn_dist.spec` is `Watch_dist.spec` plus the following:
- premises:
  - `Γ.auth = true`;
  - distinct `Γ.au`;
  - `γR.raft.log = Γ.kv.rlog`;
  - `outTokOkS (principalOf cfg) om`;
  - `clientF cl "cfg" ↦□ cfg ∗ ⌜cfg.Token' = []⌝`;
  - `watchFloorsD eps Γ γR L₀`;
- the row: the element's `Au`, `□ (⌜r.events ≠ []⌝ → watchCheckedD …)`.

`watchCheckedD` says that some `mid` with `servedBy eps Γ mid`, some `info` and some committed `L ⊒ L₀`
(`srvReqLogLb γR L`) satisfy `userOk P info.Username'` and
`auth.permitted (srvAuthAtLog Γ.kv srvAuthSt0 L) (authInfoM info) (watchKey key) rangeEnd .read`. `permitted` is
`enabled = false ∨ granted`. `granted` leaves out the revision check and is vacuous on shapes the cache does not
decide (`Model.lean:204`). Both make the claim weaker, which is safe.

## 2. Point 1: the state the create is checked at

- **The check** (`v3rpc/watch.go:239-249, 289-320`). Every `WatchCreateRequest` is checked by `isWatchPermitted`,
  which runs `AuthInfoFromCtx` of the stream's context, falls back to `&AuthInfo{}`, then calls
  `IsRangePermitted(info, Key, RangeEnd)`.
  - The check runs after `Key ""→"\x00"` and before the range end is rewritten for mvcc (`"\x00"→[]byte{}` comes
    after it, `:322-330`). So `WithFromKey` is checked as open-ended (`checkKeyInterval`), not as a point. This
    matches `watchKey` and the request's own `rangeEnd`. The negative start-revision refusal comes first.
  - A refused create gets `Created+Canceled` with `WatchId -1` and no watcher. The only call to
    `watchStream.Watch` is in this branch.
  - The client re-creates a resumed watcher with a new create, so it is checked again.
  - Progress responses (`RequestProgressAll`, broadcast id -1) and `Created` notifications carry no events.
    Fragments belong to a registered id.
  - So events go only to a watcher whose create passed. The client-side dispatch is the in-process proof's.
- **Watch is served locally.** Unlike `TimeToLive`, nothing forwards to the leader: the create is checked by the
  receiving member's own auth store, and the events come from its own mvcc store. There is no F7-style forwarding
  window.
- **A mix of states within one check** (`isOpPermitted`, `store.go:862-904`). The check reads four things:
  - the flag;
  - the revision (against the one that `AuthInfoFromCtx` stamped);
  - the user, through `lockedReadTx`;
  - the cache.

  A pass is witnessed by one of those states:
  - flag `false`: that state permits;
  - user root: the user-state grants;
  - cache covers: the cache-state has the user's entry, so the user exists there and the cache-state grants.

  The in-process proof states this as `watchClassFrom` over states recorded at indices of at least `n`.
- **Snapshot apply** (`server.go:1024-`, `authStore.Recover`, `store.go:399-418`). This is new across machines: a
  one-member process never receives a snapshot. The order is:
  1. `kv.Restore(newbe)`;
  2. `s.be = newbe`;
  3. `authStore.Recover`, which sets `as.be` under `beMu`, then the revision, then the cache from the new backend's
     read tx, and only then `enabled`.

  During it, a check can read the flag of the pre-snapshot state `S_o` and the backend, revision or cache of the
  snapshot state `S_n`. The witness argument above still applies to each read, so a pass is permitted at `S_o` or
  at `S_n`. A revision that rises between the token stamp and the check refuses (`ErrAuthOldRevision`).
  - `S_n` is the leader's backend at its applied index: `createMergedSnapshotMessage` runs in the apply loop.
    raft accepts only a snapshot above the follower's commit, so `S_n` lies ahead of `S_o`, which is at or after
    the member's floor.
  - The window between `kv.Restore` and `Recover` (KV new, auth old) is harmless to the row. The row claims only
    the create's check, at the old state, which is at or after the floor.
  - Test [b]: 42,946 refused-principal creates at the restarting member, from before its restart through its
    snapshot apply (`restoring mvcc store` → `restored auth store` → `applied snapshot` all fall inside the
    probe), got 0 events.
- **Lagging member** (test [lag]). A member stopped before `AuthEnable` and restarted after the log was compacted
  passes anonymous creates until it applies the snapshot. One such watch created before `restored auth store`
  then streamed 61 events, 60 of them written after `AuthEnable`, from the restored store. After a linearizable
  read at that member, the anonymous create is refused. So the floor must be the serving member's own. A barrier at
  member 0 (taken in the test) does not cover it. `watchFloorsD` puts one at every endpoint, which is what the
  workload's per-member barriers give (F3).
- **Auth enable/disable and the TOCTOU** across `AuthInfoFromCtx` and `isOpPermitted`:
  - disabled at the first read: `nil` → `AuthInfo{}` → enabled at the second read → `ErrUserEmpty`;
  - enabled and then disabled: the pass is at a disabled state, which `permitted` admits, with the token's user,
    which `userOk` admits.
- **Restarts** are out of scope: `Serve_dist`'s "Restarts are outside it" (first incarnation of `Γ.au mid`). A
  restart also drops the member's simple tokens: test [b] shows root's pre-restart token is `invalid auth token`
  at the restarted member. That is a refusal, so it is benign.

## 3. Point 2: the user

- **Token sources** (`AuthInfoFromCtx`, `store.go:1072-1097`): `md["token"]`, else `md["authorization"]`, then
  `ts[0]` with `Bearer ` trimmed. The client's per-RPC credential (`token`) is sent before the context's metadata,
  so it wins.
  - A named client re-authenticates with `cfg`'s user and password on every stream open (`getToken` in the stream
    interceptor, `retry_interceptor.go:121`). A refreshed token is therefore still `cfg`'s user.
  - TLS: `EtcdServer.AuthInfoFromCtx` reaches `AuthInfoFromTLS` only when `ClientCertAuthEnabled` is true
    (`v3_server.go:1207-1217`). `memberUpOnL` carries `□ (srvTLSId s -∗ False)`, the deployment runs plain
    http, and the docstring says so.
  - This fork does not retry a watch on `invalid auth token`: the refusal is a canceled response
    (test [a] `badtoken`).
- **Stream sharing** (`watch.go:330-347, 282`; `streamKeyFromCtx:1102`). A watch joins the stream of its key, which
  was opened (and is reopened) with the first context's metadata (`valCtx`). `streamKeyOf` is defined as Go's
  `%+v`, so its collisions are Go's. Test [d] on one anonymous client:
  - root-md stream first: a watch whose own metadata has no `token` key (`{"a": ["1] token:[<root>"]}`) is
    **served as root**;
  - colliding-md stream first: ten concurrent watches whose own metadata carries root's token are **all bound
    anonymous**.

  The server binds the stream's metadata, as `watchCheckOk` says. `outTokOkS` quantifies over every metadata of
  the key, so it excludes the first case. `outTokOk` of the watch's own `om` would not. `outTokOkS` is enough:
  any stream the watch can join was opened by some context of that key.
- **The attacks `outTokOk` excludes**, test [a] at every member and at the snapshot-restored member: an anonymous
  client with root's issued token under `authorization`, `authorization: Bearer …` or `token` gets c/'s events,
  served as root. u's client with `authorization=<root>` is refused, because u's own token wins.

## 4. Point 3: which member

`etcdAddrAt a Γ mid` is `∃ σ, grpcAddrAt a (etcdSvc Γ mid)`. `grpcAddrAt` is `addrProto a (grpcCliPI Svc) …`, and
an address's protocols are set once (`etcdAddr_set` consumes `addrUnset`). `etcdSvc` is opaque, so no proof can
equate `etcdSvc Γ mid` with `etcdSvc Γ mid'`. A caller therefore cannot hold the fact for two `mid`s at one
address. In the intended interpretation the table's entries are at `Γ.au mid`, which are distinct by the premise.
So the floor's `mid` at endpoint `a` is the one `Serve_dist` serves at `a` with `memberUpOnL … (Γ.au mid)`.

The statement needs no agreement law: the docstring's argument is right. It rests on the intended reading of
`etcdSvc` and on Condition C of `Serve_dist`. Both are already stated.

A caller-chosen `Γ` whose `au` names the caller owns, which is how it could mint `authFloorD`, leaves those names
unservable: `memberUpOnL` holds them exclusively, by Condition C. So no response arrives and the row is vacuous.

## 5. Point 4: `w.mu` (trigger (4) of `WatchDist.lean`)

`WatchOn_dist` locks `w.mu` exactly as `Watch_dist` does, and its post adds only the persistent `watchCheckedD`
(about `Γ`, `γR`, `eps`). Its new premises are pure or persistent and have nothing to do with the lock. The
encapsulation argument is unchanged:
- `mu` is unexported;
- the proved specs read a stream only through `wgsGuard_elim` with `watchSrvFacts`;
- the axioms that lock it say nothing of the lock;
- a program that holds `watchSrvFacts V` and `membersAt eps Γ` has endpoints nothing serves, so the row is
  vacuous there.

Mixing `Watch_dist` and `WatchOn_dist` on one watcher is covered by `outTokOkS`: a `Watch_dist` watch may open a
root-token stream, but no `WatchOn_dist` watch of that key can be proved. Trigger (4) is discharged for this axiom.
The audit row's trigger text should say "(4) reviewed for `WatchOn_dist`, `watchon-dist.md`".

## 6. Point 5: interactions and premises

- `KV_GetOn_dist`'s `readCheckedD` gives exactly `watchFloorsD`'s element for its endpoint
  (`servedBy [addr] Γ mid ∗ authFloorD …`).
- `New_user_dist` gives `cfg`.
- `outTokOkS` is provable:
  - at `om = none` (`outTokOkS_none`);
  - at the `bad` principal's `{token: [badtoken]}`: its key `map[token:[badtoken]]` has no space, so only
    one-entry maps print it, and only `token ↦ [badtoken]` does. That is the workload's burden.
- No premise is unsatisfiable for the auth workload: distinct `Γ.au` comes from P-A1, and `γR` from the start.
- The mintable ones (`Γ`, address facts, own-name floors) are covered by §4.

## 7. The fixes (exact text)

- **F1** (`WatchOnViewDist.lean`, `outTokOkS` docstring). Replace ``the key is `fmt`'s `%+v` of the map and
collides (…: `{"x": ["1] token:[t"]}` prints as `{"x": ["1"], "token": ["t"]}` does)`` with ``the key is `fmt`'s
`%+v` of the map, keys sorted, and collides (…: `{"a": ["1] token:[t"]}` and `{"a": ["1"], "token": ["t"]}` both
print `map[a:[1] token:[t]]`; Go test `notes/axiom-review/watchon-dist/`)``. Test [d]: the current example prints
`map[x:[1] token:[t]]` against `map[token:[t] x:[1]]`, which are not equal.
- **F2** (`WatchOnDist.lean` axiom docstring, "The state", after its first sentence). Add: "Across machines a
lagging member may also apply a snapshot, which no single-process run does (`applySnapshot`: `kv.Restore`, then
`authStore.Recover`, which sets the backend, the revision and the permission cache before the enabled flag). A
check that interleaves reads the pre-snapshot state or the snapshot's, piece by piece. Its pass is still
witnessed by one of them: a disabled flag, a root user, or a cache entry that covers the range (and so a user
that exists at that state). The snapshot's state is the leader's at its applied index, ahead of the member's, so
both are at or after the floor. The window between `kv.Restore` and `Recover` (KV new, auth old) checks at the old
state, and the row claims only the create's check (`notes/axiom-review/watchon-dist.md` §2, Go test [b])."
- **F3** (same bullet, end). Add: "The floor must be the serving member's own: a member that lags across
`AuthEnable` passes an anonymous create at its old state and then streams post-enable events (Go test [lag]). So
`watchFloorsD` asks for one at every endpoint, as the workload's per-member barriers give."
- **F4** (`WatchDist.lean`, `Watch_dist.wp_proof` docstring, bullet "*Any auth mode.*"). Replace it with: "*Any
auth mode.* With auth off (`memberUpL`) no create is refused. With auth on (`Serve_dist`'s `memberUpOnL` since F7
step 3), a refused create (permission denied, empty user, invalid token, old revision) is a created-and-canceled
response with its reason, the error arm. A passing create's events are the cluster's, as with auth off. No row is
claimed: `WatchOn_dist` states it."
- **F5** (`ServeDist.lean` axiom docstring). Replace "the watch streams of `Watch_dist`/`RequestProgress_dist`"
with "the watch streams of `Watch_dist`/`RequestProgress_dist`/`WatchOn_dist` (with auth on, the stream carries
the client's own token or none, and metadata meeting `outTokOkS`; the handler's refusal path is
`isWatchPermitted`'s, proved in process)".

## 8. Go test

`notes/axiom-review/watchon-dist/`: `watchon_test.go.txt` with its `go.mod`/`go.sum` (same replace targets as
`examples/go.mod`), and `output.txt`. The cluster is 3 members from `tests/v3/framework/integration`, simple tokens,
`SnapshotCount 10`, `SnapshotCatchUpEntries 5`. Both tests pass, with 0 unexpected outcomes.

| case | result |
|---|---|
| (a) every member: anonymous / u / v / anonymous+`token=badtoken` / anonymous+`authorization=Bearer badtoken` watch of `c/` from rev 1 | all canceled with 0 events (`user name is empty`, `permission denied`, `invalid auth token`) |
| (a) anonymous + root's issued token under `authorization`, `authorization: Bearer`, `token` | **served as root** (4 events), at every member: what `outTokOk`/`outTokOkS` exclude |
| (a) u's client + `authorization=<root>` | refused: u's own credential wins |
| (b) a follower stopped, 80 puts, restarted: snapshot index 134 received and applied (`restoring mvcc store` → `restored auth store` → `applied snapshot`) | 42,946 refused-principal probe creates from before the restart through the apply: **0 with events**; after a barrier, every refusal holds; root's pre-restart token is invalid there; with a fresh root token the attacks again serve root (44 events) |
| (c) u's watch of `[a, b)` from rev 1 | exactly the root-made history of `[a, b)` (puts and deletes, with revisions) at every member (5 events), and at the snapshot-restored member (45 events) |
| (d) stream-key collision | `map[a:[1] token:[<root>]]` for both metadata. Root-md stream first: the token-free colliding watch is **served as root**. Colliding stream first: all ten root-md watches are **bound anonymous**. The docstring's example does not collide (F1) |
| [lag] a follower stopped before `AuthEnable`, restarted after compaction | 2 of 13,556 anonymous creates passed at its old state (one streamed 61 events, 60 written after the enable). After a barrier at that member: refused |

Not tried: a Lean counterexample. None is possible: no Go refusal was violated under the premises. Crash
restarts are excluded by `Serve_dist`. JWT tokens and client-certificate auth are not in the deployment.

## Re-review (fixes applied)

2026-11-26. I read the staged working-tree diff of the three Lean files (no build).

- **F1 closed.** `outTokOkS`'s docstring now uses the `{"a": …}` pair, which collides in `fmt`'s sorted print, and
  cites test (d).
- **F2 closed.** "The state" now states the snapshot-apply argument: Recover's order, the witness by the
  pre-snapshot state or the snapshot's, the snapshot ahead of the floor, and the `kv.Restore`→`Recover` window.
- **F3 closed.** The same bullet says the floor must be the serving member's own, with the [lag] test.
- **The statements are unchanged.** The `Spec` file's diff only repoints its header to `notes/etcd-dist-watchon.md`,
  and no `abbrev`/`def` body changed.
- **F4 and F5 are deferred to the adoption commit.** This is recorded in the new "Review" paragraph, and it is
  acceptable: both are docstring-only edits to other trusted axioms, and neither affects this axiom's soundness.
- **Nit (optional):** the bullet labels the tests "(b)" and "[lag]"; the report uses "[b]" and "[lag]".
