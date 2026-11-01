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

## Draft

**K1. Translation** (`Code/.../v3rpc.toml`): `LeaseServer.LeaseKeepAlive` and
`LeaseServer.leaseKeepAlive`. `isClientCtxErr`, `streamFailures` and the zap calls are the watch
loop's (specs exist).

**K2. The messages** (`InvLeaseKeepAlive.lean`): `pbLeaseKeepAliveRequest` (model: `ID`),
`pbLeaseKeepAliveResponse` (model: the header `HdrM`, `ID`, `TTL`), `StreamMsg` instances as
`pbWatchRequest`'s (the received request owned).

**K3. The contract grows a third triple**: `lessorRenewOk s E γl S R`, the server's
`LeaseRenew(ctx, id)` at `S ∗ R`, the context, `authPubLbM n`, `lessorLb m`, given back, with the
answer `renewAns`: `nil` and the verdict, or a non-nil `applyErrIs` error. `raftLeaseRead :=
lessorTTLOk ∗ lessorLeasesOk ∗ lessorRenewOk`. The server's `S` widens to `E.RD ∗ lessorRdOf γl ∗
threadTok ∗ srvLgReader s ∗ srvReadReader s γr` (the unary reads frame the two readers).

**K4. The stream specification** (`kaStreamSpec γs … Dn := □ ∀ j m, Dn j m ∗-∗ kaDn … j m`): the
`j`th response
```
kaDn s E γl ci cid mid n m γs j r :=
  ∃ q, upAt γs j q ∗ ⌜r.id = q.id ∧ r.hdr.clusterId = cid ∧ r.hdr.memberId = mid⌝ ∗
    (⌜r.ttl = 0⌝ ∨ leaseCheckFrom s E (ok ci) n (fun info => leaseKeysVerdictFrom E.authMode n info γl m q.id .write))
```
answers the `j`th request (its ID), with the handler's ids; a non-zero TTL carries the renewal's
verdict at the stream's lower bounds `n`, `m`. `Up` is free (the server needs nothing of a request).

**K5. `v3rpc.LeaseServer.LeaseKeepAlive.spec`**: `leaseServerAt p s A cid mid`, `raftLeaseRead s E γl
S R` with `A.revR = R`, the stream (`srvStreamIs st γs pbLeaseKeepAliveRequest
pbLeaseKeepAliveResponse Up Dn ci cd`, `kaStreamSpec … Dn`, both tokens at `[]`), `authPubLbM n`,
`lessorLb m`, and the run's `S ∗ R`; it returns an error, with `kaStreamSpec` (as `Watch`'s: `S ∗ R`
stay with the goroutine, which may outlive the handler). `leaseKeepAlive`'s own spec: the same, the
tokens consumed, its answer ignored.

**K6. The discharge**: `raftLeaseRead_of_server` takes `EtcdServer.LeaseRenew.spec` too, and
`srvPeerRt s` (`∃ rt, peerRt ↦□ rt ∗ ⌜rt a *http.Transport⌝`) beside `srvLessorRd` etc.

**K7. `NewServer` exports `srvPeerRt s`** (a frozen spec, the user's choice): `NewServer`'s post (all
three forms, `spec`/`specM`/`specG`) gains `srvPeerRt srv`; its source is `bootstrap`'s result's
`prt` (`srv.peerRt = b.prt`, `server.go`), which `bootstrapContract` (a premise every closed result
carries) must then state is a `*http.Transport` (what `rafthttp.NewRoundTripper` returns,
`transport.NewTimeoutTransport`); the field is never written after construction, so its points-to
can be made persistent in `NewServer`'s proof.

## Margins (stated, not closed)

- The header's revision is not related to the renewal (Go's comment: no later than it); the
  response states only the ids.
- A TTL of 0 (`ErrLeaseNotFound`) carries nothing, not even authentication (the unary margin).
- When the context wins the select, the loop's error is dropped; the spec says nothing of the
  returned error.

## Not in this stage

The registration (`_Lease_LeaseKeepAlive_Handler`, the quota wrapper's promoted
`LeaseKeepAlive`, as for the unary reads); the client's keep-alive; `srvLessorRd`/`srvHeaderFacts`
from `NewServer` (still premises of the discharge).
