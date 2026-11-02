# The lease keep-alive stream at the gRPC level (item 6, second stage, 2026-11-01)

Spec-first, as `notes/lease-grpc-plan.md`. Branch `lease-keepalive`. **The user's choices
(2026-11-01)**: "Unary first, stream next" (the unary reads are done and on `lean`); **"Export from
NewServer"**: `NewServer`'s spec restated to give the server's `peerRt` field (a frozen-spec change,
for the user's review), the source of `EtcdServer.LeaseRenew.spec`'s premise.

## The Go code (`server/etcdserver/api/v3rpc/lease.go:93-158` at the pin)

- `LeaseServer.LeaseKeepAlive(stream)`: `errc := make(chan error, 1)`; a goroutine runs
  `errc <- ls.leaseKeepAlive(stream)`; the handler selects on `errc` and on
  `stream.Context().Done()`, returning the loop's error or `stream.Context().Err()`. When the
  context wins, the goroutine keeps running (its send to the 1-buffered `errc` never blocks).
- `leaseKeepAlive(stream)`, a loop: `req, err := stream.Recv()`; `errors.Is(err, io.EOF)`: return
  `nil`; another error: logged (`isClientCtxErr`, `zap`, `streamFailures...Inc()`), returned. Then
  `resp := &pb.LeaseKeepAliveResponse{ID: req.ID, Header: &pb.ResponseHeader{}}`, `ls.hdr.fill(resp.Header)`
  (before the renewal: the comment's point is that the header's revision is no later than the
  renewal's), `ttl, err := ls.le.LeaseRenew(stream.Context(), LeaseID(req.ID))`;
  `errors.Is(err, lease.ErrLeaseNotFound)`: `ttl = 0`, no error; another error: return
  `togRPCError(err)`; `resp.TTL = ttl`, `stream.Send(resp)` (an error logged and returned).

So the stream's responses answer its requests in order, one each: the `j`th response is the `j`th
request's (its `ID`), sent after the renewal of that ID returned.

## What exists

- The unary lease handlers over the contract `raftLeaseRead s E γl S R` (`InvLeaseRead.lean`),
  discharged by `raftLeaseRead_of_server` (`ServerLeaseRead.lean`).
- `EtcdServer.LeaseRenew.spec` (proved): the read resources (`E.RD`, `lessorRdOf γl`, `threadTok`,
  `srvLgReader s`, `srvReadReader s γr`), the lower bounds `n` (auth) and `m` (lessor), the context,
  and the premise `∃ rt, peerRt ↦□ rt ∗ ⌜rt is a *http.Transport⌝`; on `nil`, the key check's
  verdict `.write` (`leaseCheckFrom … leaseKeysVerdictFrom … id .write`), on an error
  `applyErrIs`.
- The generic gRPC stream (`Proof/google_golang_org/grpc/InvGrpcStream.lean`): `srvStreamIs st γs
  Req Rep Up Dn ci cd`, the receiver's and sender's tokens, `upAt`, `streamErr` and `eofIs` for
  `Recv`'s error; the watch stream (`InvWatchStream.lean`, `watchServer.Watch.spec`) is the
  precedent for a handler's spec over it (`watchStreamSpec γs … Dn := □ ∀ j m, Dn j m ∗-∗ watchDn …`).

## Draft (revised after the review, with the user's choices)

**K1. Translation** (`Code/.../v3rpc.toml`): `LeaseServer.LeaseKeepAlive` and
`LeaseServer.leaseKeepAlive` (done). `isClientCtxErr`, `streamFailures` and the zap calls are the
watch loop's (specs exist).

**K2. One wire model, the client's** (review finding 2): `pbLeaseKeepAliveRequest`/`Response`
already exist (`client/v3/InvLessor.lean`, used by the client's keep-alive proofs and
`leaseKAStreamOk`); they move to a module both ends import, and the server uses them. The response's
model is `(ID, TTL)`, read-only once sent (`keepAliveRespMsg`): the stream specification states no
header content. **The request's model gains ghost bounds** (the user's choice, 2026-11-01: "ghost
bounds per request", as watch's create `bound`): `{id, nb, mb}`, the wire carrying `id` only; the
client's content `Up j q` gives `□ authPubLbM M q.nb ∗ □ lessorLb γl q.mb` (`kaUpOk`). The client's
keep-alive specs and proofs (`lessor.sendKeepAliveLoop`, `recvKeepAliveLoop`, `resetRecv`,
`KeepAlive`, `leaseClient.LeaseKeepAlive`, `retryLeaseClient.LeaseKeepAlive`, `leaseKAStreamOk`) are
restated as callers. The client's lessor knows nothing of the server's ghost state, so the
registration's `Up` (`kaUp E γl`) comes with a law the server proves when it registers, `□ ∀ j id,
Up j ⟨id, 0, 0⟩` (the facts at `0`); `leaseKAStreamOk` becomes `∃ Up Spec, isGrpcStream … Up Spec ∗
that law`, and the client sends bounds `0` (its keep-alives carry no verdict it could use: their
posts are safety only).

**K3. The contract grows a renewal triple with its own resources** (finding 5):
`lessorRenewOk s E γl S'`, the server's `LeaseRenew(ctx, id)` at `S'`, the context,
`authPubLbM n`, `lessorLb m`, given back, with the answer `renewAns`: `nil` and the verdict, or a
non-nil `applyErrIs` error. `raftLeaseRead s E γl S R S' := lessorTTLOk ∗ lessorLeasesOk ∗
lessorRenewOk` (the unary reads' `S` unchanged; no `R` in the renewal, which never reads the store).
The server's `S' := E.RD ∗ lessorRdOf γl ∗ srvLgReader s ∗ srvReadReader s γr` (the loop's
`threadTok` is the forked goroutine's own).

**K4. The stream specification, over the run's token** (finding 1): `kaStreamSpec … tok Dn := □ ∀ j
r, Dn j r ∗-∗ kaDn … tok j r`, with
```
kaDn s E γl γs tok j r :=
  ∃ q, upAt γs j q ∗ ⌜r.id = q.id⌝ ∗
    (⌜r.ttl = 0⌝ ∨ leaseCheckT s E tok q.nb (fun info => leaseKeysVerdictFrom E.authMode q.nb info γl q.mb q.id .write))
```
the `j`th response answers the `j`th request (its ID); a non-zero TTL carries the renewal's
verdict at that request's bounds, for the run's token `tok = auth.ctxTokenOf (ok ci)` (registrable
at the metadata's token, `auth.mdTokenOf md`, as `watchDn`). `leaseCheckT` states the check over a
token (`infoBoundT`, `infoBoundT_of_principalBoundI`); `leaseCheckFrom` implies it.

**K5. `v3rpc.LeaseServer.LeaseKeepAlive.spec`**: `leaseServerAt p s A cid mid` (gaining the logger,
`lg ↦□ lg ∗ ⌜lg ≠ null⌝`, proved by `NewLeaseServer`: finding 3; an interface diff for every lease
handler), `raftLeaseRead s E γl S R S'` with `A.revR = R`, the stream (`srvStreamIs st γs
pbLeaseKeepAliveRequest pbLeaseKeepAliveResponse Up Dn ci cd`, `kaStreamSpec … Dn`, `kaUpOk Up`,
both tokens at `[]`) and the run's `R ∗ S'`; it returns an error, with `kaStreamSpec`.
`leaseKeepAlive`'s own spec: the same, the stream tokens consumed, `R ∗ S'` given back when the loop
ends (finding 7).

**K6. The discharge**: `raftLeaseRead_of_server` takes `EtcdServer.LeaseRenew.spec` too and
`srvPeerRt s`, a named predicate (`∃ rt, peerRt ↦□ rt ∗ ⌜rt a *http.Transport⌝`), which
`EtcdServer.LeaseRenew.spec`'s inline premise is restated with (same meaning).

**K7. `NewServer` exports the server's lease facts** (the user's choice, 2026-11-01: "export all
three now"; a frozen spec): `NewServer`'s post (`spec`/`specM`/`specG`) gains `srvPeerRt srv`,
`srvLessorRd srv γl` and `srvHeaderFacts srv cid mid`, so the discharge has no premise without a
source. `srvPeerRt`'s source is `bootstrap`'s `prt` (`srv.peerRt = b.prt`, `server.go:330`), which
`bootOk` then states is a `*http.Transport` (a pure conjunct; Go: `rafthttp.NewRoundTripper`,
`transport.NewTimeoutTransport`, `bootstrap.go:72`); the field is never written after construction.
`srvLessorRd` from `NewLessor`'s `lessorInv` (in `NewServer`'s proof today); `srvHeaderFacts` from
the cluster, member id and leader-invariant facts the proof builds. Restated as callers: the
corollaries `wp_proofM`/`wp_proof`, the examples carrying `bootstrapContract` (stronger premise,
proofs unchanged), and the callers destructuring the post (`examples/authkv/startServer.lean`,
`examples/common/newServer.lean`, ...; counted with `etc/importers.py` at the Probe).

## Margins (stated, not closed)

- No header content is stated (the wire model's), so nothing about its revision. Go's comment says
  the revision is no later than the renewal's. It holds (finding 9, checked 2026-11-01): on a
  follower `fill` reads the local revision, of entries the leader had committed, and the forwarded
  renewal waits at the leader for its applied index to reach its commit index
  (`leasehttp/http.go:85`, `h.waitch()`, which is `EtcdServer.ApplyWaitCommit`, `server.go:634`)
  before `Renew`; on the leader `LeaseRenew` waits too (`waitAppliedIndex`). No `issues/` entry.
- A TTL of 0 (`ErrLeaseNotFound`) carries nothing, not even authentication (the unary margin).
- Nothing of the renewal itself (that the lease was renewed, its TTL): `LeaseRenew.spec` states none.
- The verdict is of the local member's lessor, which on a follower can lag the leader's
  (`issues/etcd-lease-renew-keys-follower-lag.md`): not the cluster's certificate.
- A failed `Send` may have delivered its response; the content was spent either way.
- When the context wins the select, the loop's error is dropped.

## Not in this stage

The registration (`_Lease_LeaseKeepAlive_Handler`, the quota wrapper's promoted `LeaseKeepAlive`;
grpc's one per-run `S` for every stream method, to be combined with `watchRunSlot`: finding 6); the
client's keep-alive beyond restating it.

## Review (2026-11-01, an independent spec-reviewer)

Nine findings; the Draft above is revised for 1-8: (1) the stream spec named the run's `n`, `m` and
context, unregistrable (fix: token form, per-request ghost bounds); (2) a second wire model for
the client's messages (fix: one shared); (3) the loop logs but `leaseServerAt` had no logger; (4)
exporting `peerRt` alone closed nothing (fix: all three, the user's choice); (5) the shared `S`
widened with reader slots the unary reads do not use (fix: `S'`); (6) the registration's single
stream slot (recorded); (7) `leaseKeepAlive` should give back its resources; (8) missing margins;
(9) the header-revision comment may not hold in Go (to check).

## Probe (2026-11-01)

Built (`lake build` of each module):
- **K2**: the wire model moved to `Proof/go_etcd_io/etcd/api/v3/etcdserverpb/LeaseKeepAliveMsg.lean`
  (`KaReqM := {id, nb, mb}`); the client restated (`kaUpZero`, `leaseKAStreamOk := ∃ Up Spec, … ∗
  kaUpZero Up`; `leaseClient.LeaseKeepAlive`, `retryLeaseClient.LeaseKeepAlive`, `resetRecv`,
  `sendKeepAliveLoop` (sends bounds `0`), `recvKeepAliveLoop`): all re-prove. `leaseKAStreamOk` is
  only ever a premise (the client's closed results'), so its stronger meaning breaks no proof.
- **K3-K4**: `InvLeaseKeepAlive.lean`: `infoBoundTM`, `leaseCheckT` (with `leaseCheckT_of_from`,
  proved), `kaUp`, `kaUpOk`, `kaDn`, `kaStreamSpec`, `renewAns`, `raftLeaseRenew` (a separate
  contract, not a third parameter of `raftLeaseRead`: the unary handlers' specs are untouched).
- **K5**: `leaseServerAt` gains the logger; `NewLeaseServer` re-proves (the `wp_join` of
  `NewWatchServer`). The handler specs `LeaseServer.LeaseKeepAlive.spec`/`leaseKeepAlive.spec`
  typecheck (proofs `sorry` for now).
- **K6**: `srvPeerRt` (`LeaseRead.lean`); `EtcdServer.LeaseRenew.spec`'s premise restated with it,
  re-proved; `raftLeaseRenew_of_server` proved from `EtcdServer.LeaseRenew.spec`.
- **K7** (mapped, read-only, not yet changed): `NewServer`'s proof has `srvLessorRd`'s facts
  (`NewLessor`'s `lessorInv`, the `lessor` field `↦□`) and the `peerRt` field (owned, one `ipersist`);
  `bootOk` needs the pure conjunct on `bs.prt'`. **`srvHeaderFacts` needs no `NewServer` change**: it
  follows from `isServerReqM` (`srvReqFieldsAtM`: `memberID`, `cluster`, `lead`, `srvPeersOk`'s
  `clusterCid`), which the discharge already takes: a law (`srvHeaderFacts_of_reqM`), not a
  frozen-spec change. Restated callers: `NewServer.spec{,M,G}`'s posts and `wp_proof`,
  `examples/common/newServer.lean` (2 places), `examples/authkv/startServer.lean`; the examples'
  `bootstrapContract` premises get stronger, their text unchanged.
- **Found** (no source anywhere, for a later stage): `srvAuthLeaseLb s E` (a premise of every lease
  discharge); `NewServer` drops `NewLessor`'s remaining `lessorRdOf` slots (`NewServer.lean:621`), so
  no run slot can supply the renewal's `lessorRdOf γl` yet.

## Freeze (2026-11-01, the user's)

Approved: K2-K6 as in the Probe (the wire model's ghost bounds shared by both ends, `leaseKAStreamOk`
over `kaUpZero`, `kaDn`, `leaseServerAt`'s logger, `srvPeerRt`), with the margins; `srvHeaderFacts`
by a law from `isServerReqM` (not exported); K7: `bootOk` states `prt` a `*http.Transport` and
`NewServer`'s three forms export `srvPeerRt` and `srvLessorRd`.
