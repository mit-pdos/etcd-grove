# `EtcdServer.leaseTimeToLive`: refuted as documented (premise gap, 2026-11-02)

**Reviewed.**
- The trust-boundary axiom `EtcdServer.leaseTimeToLive.wp_proof`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__leaseTimeToLive.lean`), its triple
  `EtcdServer.leaseTimeToLive.spec`
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__leaseTimeToLive.lean`), as restated on
  branch `lease-ex` in `c11e0942a3`: the success arm gained `⌜w.ID' = v.ID'⌝`, and the docstring's
  cluster assumption became "whatever serves `/leases/internal` at the leader's peer URLs answers
  200 only with a `LeaseTimeToLiveResponse` and its header set".
- The whole triple, not only the new conjunct: the error set, the header facts, the resources
  (`lessorRdPool`, `threadTok`, `r ↦{dq} v`), the leader path and the follower path.
- etcd at the pin (the fork's `ab3c28d`, `.lake/goose/etcd`): `server/etcdserver/v3_server.go:636-696`
  (`leaseTimeToLive`), `:785-803` (`waitLeader`), `:458-468` (`waitAppliedIndex`),
  `server/lease/leasehttp/http.go:226-278` (`TimeToLiveHTTP`).
- Branch `axiom/lease-ttl-id`, off `lease-ex` at `c11e0942a3` (the restated axiom exists only there).

**Verdict.**
- **Refuted as documented**, by a proved counterexample. The axiom's docstring states an assumption
  on the cluster (what answers the leader's peer URLs), but the triple has no premise for it, and a
  program can serve its own member's peer address with anything.
- A program whose peer listener answers every request `200` with an empty body panics in Go on the
  follower path (`TimeToLiveHTTP`'s nil dereference, `issues/etcd-leasehttp-timetolive-nil-response-panic.md`).
  The axiom proves it returns. No `sorry` beyond the four every started member's proof reaches
  (putget's).
- **The new conjunct `⌜w.ID' = v.ID'⌝` survives**: true on both paths whenever the call returns.
- The error set, the resources and the leader path survive. The header conjunct on the follower
  path falls with the same gap: a reply carrying a response without a header returns `Header == nil`.

## The claim

`s.leaseTimeToLive(ctx, r)`, from the server's request and read facts, its lessor
(`srvLessorRd s γl`), the lessor's reader pool, a thread token and `r ↦{dq} v`, returns the token
and `r ↦{dq} v`, and either:
- `nil` and a fresh, owned response `w` whose `Header'` is not nil and owned and whose `ID'` is
  `v.ID'`; or
- `null` and an error with `applyErrIs`.

It never panics. The docstring's argument is per path:
- the leader's response is a literal with `ID: r.ID` and `Header: &pb.ResponseHeader{}`;
- a follower's is `TimeToLiveHTTP`'s reply from the leader's peer URL, whose ID `TimeToLiveHTTP`
  checks (`http.go:274`), and whose response and header etcd's lease handler always sets.

The last part is stated as the triple's "assumption on the cluster", in prose only.

## The gap

`leaseTimeToLive` is names-only: the model has no round trip for the follower's
`TimeToLiveHTTP`. The triple holds for any program that meets its premises, whatever serves the
leader's peer URLs. In Go, a follower:
1. waits for a leader (`waitLeader`: the member `s.Leader()` names, or `ErrNoLeader`/`ErrStopped`);
2. POSTs to each `PeerURL + "/leases/internal"`;
3. on a `200` with a body that unmarshals to a `LeaseInternalResponse` without a
   `LeaseTimeToLiveResponse` (the empty body does), dereferences it at `http.go:274`: a panic on
   the caller's goroutine.

Nothing in the premises says who serves those URLs. In a one-member cluster the member is its own
leader once elected, and is a follower until then (`isLeader()` reads `s.Lead()`, which is `0`
before the first election). So the program needs only its own peer address, which it owns at
start (`netAddrFree`, `httpProtoFree`).

## The counterexample

`examples/axiomcx/leasettl/leasettl.go` (project `axiomcx-leasettl` of `etc/goose.py`, on the branch
only). `Main`:
1. `net.Listen("tcp", peerAddr)` and `go http.Serve(l, &okHandler{})`, where `okHandler.ServeHTTP`
   is `w.WriteHeader(http.StatusOK)`;
2. `common.StartServer("leasettl", peerAddr, clientAddr, zap.NewNop())`, which serves nothing on
   the peer address;
3. `go holdToken()` (its thread token, as `leasekv`'s);
4. `s.LeaseTimeToLive(ctx, &pb.LeaseTimeToLiveRequest{ID: 7})` at once, in a 5-second context.

**Go** (`leasettl_test.go`, go1.27.3, the examples' module at the pin): 5 of 5 runs, one per
process (the address is fixed):

```
leasettl_test.go:17: Main panicked: runtime error: invalid memory address or nil pointer dereference
  go.etcd.io/etcd/server/v3/lease/leasehttp.TimeToLiveHTTP(...)  lease/leasehttp/http.go:274
  go.etcd.io/etcd/server/v3/etcdserver.(*EtcdServer).leaseTimeToLive(...)  etcdserver/v3_server.go:682
  go.etcd.io/etcd/server/v3/etcdserver.(*EtcdServer).LeaseTimeToLive(...)  etcdserver/v3_server.go:713
```

The call starts before the first election. `waitLeader` sleeps one election timeout (1s) and
returns the member itself. `TimeToLiveHTTP` then gets `okHandler`'s `200`. No interleaving needs
forcing: the election takes at least a tick after `Start`.

**Lean** (`Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/leasettl/Main.lean`, built by
`lake build`, no `sorry` in the file):
- `Main.spec`: `{{ isPkgInit leasettl ∗ netAddrFree peer ∗ httpProtoFree peer ∗ threadTok ∗
  premises … }} Main #() {{ RET #(); True }}`. Its pure and named premises are `leasekv`'s `Main`'s:
  - `BootFacts`;
  - the bounds;
  - `ckptEffectsOk`, `authRecordsFit`, `backendUnderQuota`, `diskOk`;
  - `bootstrap`'s and the raft wrapper's contracts;
  - `runsNoRequireLeader`.
- `Main.wp_proof`: from the callees' specs. The steps:
  - `net.Listen`;
  - the peer address's protocol fixed (`http.reserve`, `http.register`) as `cxProto`: any request,
    any response;
  - `http.Serve_ok` with `okHandler` proved a handler of it (`WriteHeader(200)` by
    `respWriteHeader_ok`);
  - `common.alloc1`, `common.StartServer`, `holdToken` (`wp_fork_tok_self`), `WithTimeout`;
  - the server's facts from `memberUp`: `srvAuthAt_of_views`, `srvAuthLb_off`,
    `srvAuthLeaseLb_of_server`, `lessorLb_get`, `authPubLbM_zero`;
  - `EtcdServer.LeaseTimeToLive.spec`, `cancel()`.
- `Main.wp_of_axiom (hTTL : EtcdServer.leaseTimeToLive.spec)`: `Main.wp_proof` at the linked
  results, with `EtcdServer.LeaseTimeToLive.wp_proof … hTTL …`.
- `Main.wp_axioms`: the same at the axiom.

`#print axioms Main.wp_axioms`: 1893 lines, the whole server's trust base, kept in the build log. It
was compared mechanically with `putget.wp_Main` (a closed example's linked `Main`, the same member
start) by walking both proofs' constants.
- Axioms in `leasettl` and not in `putget`: `EtcdServer.leaseTimeToLive.wp_proof` (the axiom under
  review) and the HTTP boundary's `http.Serve_ok`, `http.respWriteHeader_ok`, `http.reserve`,
  `http.register`, `httpProtoFree`. Those five are the ones `common.NewMember`'s proof uses, and the
  program uses them as their statements intend:
  - a protocol of its own choice for an address it owns;
  - a handler that answers every request of that protocol with a final status.
- `sorryAx`: reached through the same four `sorry`s as `putget.wp_Main` (`run_job_snap_cmp`,
  `txn.kvWriter_noCmp`, `txn.kvWriter_keyObs`, `merged_image`, all in `etc/tcb-baseline.txt`). They
  are in the started member's apply loop and snapshot paths, and none is about leases or HTTP.
- `Main.wp_of_axiom` prints the same set minus the axiom under review.

So the counterexample adds nothing to what a proved example already rests on, except the axiom
under review and the HTTP boundary a multi-member example uses.

Which statement is wrong? The HTTP boundary says a handler of address `a` gets only requests of
`a`'s protocol (`cxProto` admits all). `okHandler` is a faithful handler of it, and Go's `Serve`
does call it. The false claim is the axiom's: a follower survives whatever answers its POST.

## Attacks tried

1. **The follower path, a peer URL that answers 200 without a response** (above). **Works.**
2. **The follower path, a 200 with a response but no header.** In Go, a handler that writes
   `proto.Marshal(&leasepb.LeaseInternalResponse{LeaseTimeToLiveResponse: &pb.LeaseTimeToLiveResponse{ID: id}})`
   makes `leaseTimeToLive` return a response with `Header == nil`. The triple says `w.Header' ≠ null`.
   - It is the same gap, and the program to check it (`if resp.Header == nil { panic(...) }`) needs
     the program to marshal the reply. Not built.
   - `issues/etcd-leasehttp-timetolive-nil-header-panic.md` records where a nil header panics
     downstream (the gRPC handler's `fill`).
3. **The new ID conjunct.** It survives.
   - Leader: the literal's `ID: r.ID`, and `r` is held at `v` for the whole call.
   - Follower: `TimeToLiveHTTP` returns only after `lresp.LeaseTimeToLiveResponse.ID ==
     int64(lease.LeaseID(r.ID))`, an identity conversion (`int64` both). Any other ID is an error,
     which `leaseTimeToLive` skips (it is not `ErrLeaseNotFound`), trying the next URL or looping
     until the context ends.
   - No path returns a response it did not check.
4. **The error set (`applyErrIs`).** It survives. `applyErrIs` asks for an error tree with exact
   `Is`/`Unwrap` relations, `nil` or a safe map key whose `Error()` returns. Every error returned is
   an `errors.New` sentinel (a pointer leaf):
   - leader: `ErrStopped`, `ErrTimeoutWaitAppliedIndex` (`waitAppliedIndex`), `lease.ErrLeaseNotFound`,
     `ErrLeaderChanged`;
   - follower: `ErrStopped`, `ErrNoLeader` (`waitLeader`, also on a member without peer URLs),
     `ErrTimeout`, `ErrCanceled`, and `TimeToLiveHTTP`'s `err` when `errors.Is(err, ErrLeaseNotFound)`.

   That last one is the sentinel itself: `TimeToLiveHTTP` returns `lease.ErrLeaseNotFound` on a
   404. Its other errors are a `*url.Error` over the peer transport's errors, `fmt.Errorf("%w")` of
   a protobuf error, or `fmt.Errorf` strings; none wraps the sentinel. Every error return is
   `nil, err` (`resp = null`).
5. **The header on the leader path.** It survives: a fresh `&pb.ResponseHeader{}`, owned. On the
   follower path with etcd's lease handler, the header is set to an empty message, which
   protobuf-go encodes (a present message field). The decode gives a fresh non-nil header, as the
   lease example's three-member test confirms (78 answers, `leasekv_cluster_test.go`).
6. **The resources.** They survive.
   - `r ↦{dq} v` is only read (`r.ID`, `r.Keys`) and not retained: the follower marshals a new
     request.
   - `lessorRdPool` is persistent.
   - The token is returned on every path.
   - The leader's reads take the lessor's lock one at a time through the pool (`Lookup`), then
     each lease's own lock (`Remaining`, `TTL`, `Keys`, `Demoted`), each released before return.
   - The follower takes no lessor lock. Its HTTP client's goroutines take none either.
7. **The leader path's panics.** It survives.
   - `le.Remaining().Seconds()` converted to `int64` (a forever lease's `math.MaxInt64` nanoseconds
     is about `9.2e9` seconds, in range).
   - `make([][]byte, len(ks))` with `len(ks)` a real slice's.
   - The lessor is non-nil (`srvLessorRd`'s `lp ≠ null`).
8. **Non-termination** (no peer URLs, a leader that never answers): the loop runs until the
   request's timeout. It is partial correctness, not a counterexample.

## What rests on it

- `EtcdServer.wp_LeaseTimeToLive` (server `Link.lean`).
- Through it, `v3rpc.raftLeaseRead_server` (`api/v3rpc/Results.lean`), the gRPC handler's
  `LeaseTimeToLive`, the client's `lessor.TimeToLive` in `leasekv`'s chain
  (`common.kv_lease_served`, still a `sorry` on `lease-ex`) and `leasekv`'s `Main`/`leasekv_safe`.
- Collections: `server.txt` (the axiom is in its baseline), `leasekv.txt`.

None of these is refuted by this program: each still needs its own premises (leasekv's `Main` does
not serve its peer address at all; a refused connection is an error the loop skips). But each
inherits a triple that is false in deployments the premises admit.

## Proposed restatement (not applied: the user's decision)

Make the cluster assumption a premise, so that a program serving the leader's peer URLs with
anything else cannot use the triple. Two shapes:

- **(A) a named deployment fact** (as `v3rpc.runsNoRequireLeader`, D19a's kind): an opaque
  persistent `srvLeasePeersOk s`, read "every peer URL of every member of `s`'s cluster answers a
  POST to `/leases/internal` with `200` only with a `LeaseInternalResponse` whose response and
  header are set (etcd's `leasehttp.NewHandler`), or not with 200 (404 where nothing serves the
  path)". `leaseTimeToLive.spec` and `LeaseTimeToLive.spec` take it, and `raftLeaseRead_server` and
  `kv_lease_served` thread it to `leasekv`'s `Main` premises.
  - A program like this one cannot discharge it. A closed theorem that assumes it is vacuous for
    such a deployment, as intended.
  - Cheap: no model change.
- **(B) over the HTTP model**: for every member `m` of the cluster and every peer URL of `m`, its
  host has a registered protocol (`httpProtoAt host P`) whose `P.resp R γk 200 w`, at
  `R.path = "/leases/internal"`, implies `w` decodes to a `LeaseInternalResponse` with its response,
  header and `R`'s ID set.
  - This is checkable by the program that registers the address, so it is stronger than (A): the
    proof, not the reader, checks the deployment.
  - It needs `raftProto` (the examples' peer protocol) to say what a non-raft path answers: Go's
    `ServeMux` 404. That is a change to `Stream.lean`'s `raftProto.resp`, and `NewMember`'s proof
    keeps working.
  - It makes the follower's round trip part of the model in name, though still not proved.

The new conjunct `⌜w.ID' = v.ID'⌝` needs no change under either.

Independently, the Go fix in the issue (`TimeToLiveHTTP` returning an error on a missing
response) would make the follower path's no-panic claim true unconditionally. With it, the
header conjunct alone would still need the premise, or a weaker post (`w.Header'` possibly nil,
which the gRPC handler's `fill` would then have to handle).

## Outcome (2026-11-02)

The user chose (A). On `lease-ex`, `leasePeersOk : Prop` (`etcdserver/LeaseRead.lean`, `opaque`, as
`grpcRepliesFit`) is a premise of `EtcdServer.leaseTimeToLive.spec` and of
`EtcdServer.LeaseTimeToLive.spec`, `raftLeaseRead_of_server`/`raftLeaseRead_server`,
`common.kv_lease_served`, `leasekv.Main.spec` and the hypotheses of `leasekv_adequate`/`leasekv_safe`.
The counterexample's `Main.wp_axioms` no longer goes through without assuming it, which its program
falsifies. The counterexample stays on `axiom/lease-ttl-id`.
