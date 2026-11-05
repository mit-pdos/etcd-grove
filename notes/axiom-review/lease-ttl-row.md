# `EtcdServer.leaseTimeToLive`, E2 revision 5 (the lease-TTL row): survives (2026-11-05)

**Reviewed.**
- The trusted triple `EtcdServer.leaseTimeToLive.spec`, as E2 revision 5 of
  `notes/lease-expiry-plan.md` restates it ("Proposed, awaiting the user (trusted): E2, revision 5,
  exact text"; decided by the user 2026-11-05). This is the text the plan proposes, not the file:
  at `f5eec16dd1` (branch `lease-expiry`), `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__leaseTimeToLive.lean`
  still has the unrestated triple. Its vocabulary: `leaseTTLRow s γl`, `nodeStartedFresh`,
  `errIsTrue`, and `lease.leaseTTLAt`/`leaseAbsentFrom`/`lessorLb`/`lessorAt`
  (`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean:379-418`).
- The claims under the row, which says that `s`'s node `n` was made by `StartNode` with voters
  `[mid]`, every committed index's configuration is `simple {mid}`, and the lessor's history begins
  empty:
  - **found**: `∃ i ≥ m, leaseTTLAt γl i id GrantedTTL`, or `leaseAbsentFrom γl m id`;
  - **not found** (`errors.Is(err, ErrLeaseNotFound)`): `leaseAbsentFrom γl m id`, where
    `leaseAbsentFrom γl m id` means *some* index `i ≥ m` has no lease `id`.
  - The rest of the triple (resources, header, `ID`, `applyErrIs`) is as before:
    [lease-ttl-id](lease-ttl-id.md) reviewed it, and `leasePeersOk` repaired it.
- etcd at the pin (`673da07c8`, the fork's `goose-lean-noproph2`, read in `.lake/goose/etcd`):
  - `server/etcdserver/v3_server.go:636-696` (`leaseTimeToLive`), `:458-468` (`waitAppliedIndex`)
    and `:785-803` (`waitLeader`);
  - `server/etcdserver/raft.go:184-241` (`updateLead` before the `applyc` send);
  - `server/etcdserver/server.go:705-727` (`Process`), `:1268-1291` (`isLeader`, `MoveLeader`)
    and `:1735` (`setLead`, its only writer);
  - `server/lease/lessor.go:281-325` (`Grant`: `ttl` written before the map insert);
  - `server/etcdserver/bootstrap.go:53-125`.
- raft at the pin (`565c2bd`): every `becomeFollower`/`becomeCandidate` site of `raft.go`
  (`:487, 1052-1057, 1145-1147, 1302, 1703-1725, 1889, 2004`), `:967-969` (the leader always
  `RecentActive`) and `:1667-1669` (a transfer to self is ignored).
- Branch `axiom/leasettl`, off `lease-expiry` at `f5eec16dd1` (where revision 5's text is).

**Verdict.**
- **Survives.** No Go run makes either arm false while the row holds.
- Both arms rest on one Go fact: under the row, `isLeader()` reads false only while the lessor has
  never held a lease. After that, the found arm's leader path and the not-found arm's leader path are
  plain lookups.
- The fact holds because of the following:
  - The lead is stored before any committed entry reaches the apply loop.
  - A sole voter never leaves leadership through any path a member can take.
  - The only way out is a message from outside the cluster's ghost network, which the trusted
    transport contract (decisions.md D21b (A)) excludes and which no verified program can produce.
- Go tests of the startup window, of `MoveLeader` churn and of that outsider message are in
  `examples/axiomcx/leasettlrow/` (tests only, no Goose project).
- The outsider test confirms that the margin the docstring names is load-bearing: a forged
  higher-term `MsgApp` makes `TimeToLive` answer not found for a live lease.

## The Go argument, checked

1. **Leader path (no row needed).** `isLeader()` is true, then `waitAppliedIndex`, then `Lookup`.
   - `Lookup` reads the current lease map, whose history index is at least the caller's `m`
     (`lessorLb γl m`, monotone).
   - `nil` gives `ErrLeaseNotFound`, and the id is absent at that index.
   - Otherwise `GrantedTTL = le.TTL()`, the `ttl` field. `Grant` writes it before the map insert
     (`lessor.go:301-310`, after the minimum-TTL adjustment), and nothing writes it later
     (`Checkpoint` only reads it, `:794`). This is the `leaseTTLAt` at that index.
   - The leader path's other errors are distinct `errors.New` leaves with no `Is` method:
     `ErrStopped` and `ErrTimeoutWaitAppliedIndex` (`waitAppliedIndex`), and `ErrLeaderChanged` (a
     demoted lease). `errIsTrue` against `ErrLeaseNotFound` is refutable for them.
2. **Forwarded path (`isLeader()` false at the check).** Both arms follow from "the lessor had no
   lease at the check" (an index `≥ m`), whatever the forwarded reply is.
   - **The lead is stored first.** `setLead` has one writer, `updateLead` from `rd.SoftState`. In
     each `Ready` it runs before `applyc <- ap` (`raft.go:202` vs `:240`). The lessor gains leases
     only through applied grants: a first start's backend is empty (`bootOk`'s fresh data
     directory) and has no snapshot. Before the leader exists, raft drops proposals
     (`raft.go:1699-1701`). So an atomic load of `lead` that sees `≠ mid` precedes every `Grant`.
   - **A sole voter, once leader, stays leader.** Every `becomeFollower` site of raft at the pin
     needs one of the following:
     - a higher-term message from another node (`:1145-1147`);
     - a lost quorum (`:1302`), but the leader counts itself always active (`:967-969`), and the
       voters are `{mid}`;
     - a lost pre-vote or vote (`:1725`), which only candidates have;
     - a snapshot restore as leader (`:1889`);
     - removal from the configuration (`:2004`), which `confAt … {mid}` excludes.

     The etcd server's own leadership calls do not change this:
     - `MoveLeader(self)` passes the member check and raft ignores it (`:1667-1669`);
     - `MoveLeader(non-member)` is refused by `server.go:1274-1277`, and raft would drop it anyway
       because the target has no progress;
     - the shutdown transfer is skipped for a single voter (`server.go:1322`);
     - etcd calls neither `Campaign` nor `ForgetLeader`.
   - Under the row, the forwarded path is the startup window only. `waitLeader` can return only
     `Member(Leader())`, a member. The only member is `mid`, so the forward goes to the member's own
     peer URL, after its own election.

## Attacks tried

| # | attack | Go program / reading | outcome |
|---|---|---|---|
| 1 | Startup window: `TimeToLive` before the first election, concurrent with the first grant; a not-found or wrong `GrantedTTL` for a call begun after the grant returned | `TestStartupWindow`: one member as `NewMember` serves it (raft handler only, `/leases/internal` → 404), 8 goroutines × 40 calls from `s.Start()` on, `LeaseGrant(ID 7, TTL 60)` once leader; 5 fresh members | 1600 calls; 40 not-found answers, all from calls begun before the grant (forwarded, lessor empty: the row's case); **0 violations** |
| 2 | Leadership loss through `MoveLeader` (to itself, which the member check admits; to a non-member) | `TestSelfMoveLeader`: 2000 `TimeToLive`s of a live lease against continuous `MoveLeader` calls | all found, `GrantedTTL = 60`; leadership never left |
| 3 | CheckQuorum, PreVote, `MsgTimeoutNow`, restore-as-leader, removal | raft reading (above) | each needs another node, a lost vote or a configuration change: excluded by `confAt … {mid}` and the transport contract |
| 4 | An outsider's higher-term message (round 1's R1) | `TestOutsiderDeposes`: `s.Process(MsgApp{From: 0xdead, To: mid, Term: 1000})`, what the raft handler does with any POST to `/raft` that carries the cluster id and a compatible version (`rafthttp/http.go:103-148`); then `TimeToLive` of a live lease | **`lease not found` while `LeaseLeases` still lists the lease.** The path: `lead = 0xdead`, the call forwards, `waitLeader` waits out the re-election, the forward goes to the own peer URL, which answers 404. Excluded by D21b (A); not reachable by a verified program (see below) |
| 5 | Errors that `errors.Is` could match: `waitLeader` (`ErrStopped`, `ErrNoLeader`), the timeout's `ErrTimeout`/`ErrCanceled`, a caller's custom context whose `Err()` is `ErrLeaseNotFound` | reading | the leader path returns no context error. A forwarded error, matching or not, falls under "lessor empty at the check" |
| 6 | Found arm: a `ttl` other than the recorded one (the minimum-TTL rewrite, `Checkpoint`, `Promote`) | reading `lessor.go` | `ttl` is written only before the map insert (`Grant`, `Recover`). Promote and Checkpoint change only expiry and `remainingTTL` |
| 7 | Server stopped, or built and never started (`BuildServer` also returns the row) | reading | a stopped leader: `waitAppliedIndex` returns `ErrStopped`. Never started: `lead = 0`, the call forwards, `waitLeader` returns `ErrNoLeader`, and the lessor is empty |
| 8 | `lessorAt γl 0 ∅` holds but a lease enters before leadership (a first start over an old backend: a dedicated WAL directory that is fresh, or the WAL deleted, while `member/snap/db` holds leases; `bootstrap` uses `StartNode` and `NewLessor` recovers them) | reading `bootstrap.go:76-125` | **outside this spec.** Go does run this way (an old `db` without a WAL is accepted when `NewCluster` is set), but `bootstrapContract` (a premise) gives an empty backend only for a fresh data directory (`bootOk`'s `HD`, "the environment assumption"), and `NewLessor` takes an empty bucket. The row's "history begins empty" is not what carries the argument; "empty until leadership" is, through `bootOk`. Noted for whoever revisits the row when restarts recover leases (revision 5 says so) |

**Why a verified program cannot forge attack 4.**
- `EtcdServer.Process.spec` takes `netRecv γn id γd ml`, a message received from the ghost network.
- No Perennial or repository spec gives an HTTP client (`http.Post`, `Client.Do`) or raw TCP writes.
- gRPC's `NewClient` speaks HTTP/2, which the members' `http.Serve` peer listeners do not.
- So the run of attack 4 exists only with an environment outside the deployment the transport
  contract describes.

## Not tried

- A Lean counterexample: no Go run contradicts the restated triple.
- Multi-member or restarted clusters: the row excludes them, and the docstring says they need a
  restatement.
- The wrapper `LeaseTimeToLive`'s obligations: refuting `errIsTrue` for `requireAuthInfo`'s
  errors, the keys check and `ErrAuthOldRevision`. Proof obligations, not trusted.

## Reproducing

```
cd examples && PATH=$PATH:/usr/local/go/bin GOTOOLCHAIN=go1.27.3 TMPDIR=/shared/tmp \
  go test -count=1 -v ./axiomcx/leasettlrow/
```

Ports 23993-23999 (peer, one per member, since `NewMember` never closes its listener), 23992 (the
client URL, not served).
