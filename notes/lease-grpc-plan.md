# The lease rows at the gRPC level (item 6 of the lessor/auth list, 2026-11-01)

Spec-first, as `notes/lease-renew-plan.md`. Branch `lease-grpc`. **The user's choice (2026-11-01):
"Lease rows at gRPC level"**: v3rpc's lease handlers over the proved entry points, as the KV rows
are (`notes/auth-matrix.md`, rows 32-34; "the class at the handler level" was the open item after
the lease-keys plan).

## Scope (2026-11-01; the user's choices)

**The user (2026-11-01): "Unary first, stream next"**: this stage, `LeaseTimeToLive` and
`LeaseLeases` (rows 32-33), the contract and its discharge in both auth modes; the keep-alive
stream (row 34) the next stage. **"Export from NewServer"**: there, `NewServer`'s spec restated to
give `peerRt` (a frozen-spec change, for the user's review).

**What exists.** `v3rpc/lease.go`'s `LeaseGrant`/`LeaseRevoke` and the quota wrapper's are
translated and proved (`InvLease.lean`, the client lease's stage (c)) over a contract,
`raftLessor s E S` (the server's `LeaseGrant`/`LeaseRevoke` triples at a run slot `S`), that nothing
discharges: the server side through `raftRequest` waits on the lease workload. The KV handlers are
over `raftKV s A`, discharged from the linked server specs by `raftKV_of_server`
(`ServerKV.lean`) and `raftKV_of_serverOn` (`ServerKVOn.lean`, with the auth class). The three read
entry points are proved (`EtcdServer.LeaseTimeToLive`, `LeaseLeases`, `LeaseRenew`), with their key
checks' verdicts on success.

**The handlers** (`server/etcdserver/api/v3rpc/lease.go:62-158` at the pin):
- `LeaseServer.LeaseTimeToLive`: the server's call; on `ErrLeaseNotFound` (`errors.Is`) a fresh
  response `{Header, ID: rr.ID, TTL: -1}`; another error through `togRPCError`; the header filled.
- `LeaseServer.LeaseLeases`: the same, an empty listing on `ErrLeaseNotFound`.
- `LeaseServer.LeaseKeepAlive`: a goroutine runs `leaseKeepAlive(stream)` into a 1-buffered `errc`;
  the handler returns its error or, when the stream's context is done first, the context's error
  (the goroutine keeps running and its send to `errc` does not block). `leaseKeepAlive`: loop
  `stream.Recv()` (EOF: `nil`; other errors logged and returned), a response with a filled header,
  `LeaseRenew(stream.Context(), id)` (`ErrLeaseNotFound` becomes TTL 0), `stream.Send`.
- The registered service is `*quotaLeaseServer`; the three are its embedded `pb.LeaseServer`'s,
  promoted.

**The proposed shape** (the KV's): a second contract `raftLeaseRead s A` (the server's
`LeaseTimeToLive`, `LeaseLeases`, `LeaseRenew` at answers `A`), the handlers' specs over it, and
`raftLeaseRead_of_server[On]` from the three proved specs. On success the handler's answer carries
the entry point's verdict (`leaseCheckFrom ... leaseKeysVerdictFrom`, `.read` for the two reads,
`.write` per renewal); `raftLessor` stays as it is (Grant/Revoke wait on the workload).

**Open questions for the Draft:**
- The entry points take per-call resources (`E.RD`, `lessorRdOf`, `threadTok`, `srvLgReader`,
  `srvReadReader`) that the KV contract carries in its run slot; the lease contract must hand
  them over the same way.
- `LeaseRenew.spec`'s `peerRt` premise: `NewServer`'s frozen spec does not state the field; the
  keep-alive needs it exported (a frozen-spec change) or carried as the contract's premise.
- The keep-alive stream needs `Lease_LeaseKeepAliveServer`'s `Recv`/`Send`/`Context` specs (the
  watch stream's gRPC model, `InvWatchStream.lean`, is the precedent) and a goroutine whose error
  may be dropped.
- `ErrLeaseNotFound` turned into a success: on that path the handler's answer has no verdict (the
  entry point's error post is `applyErrIs`), only that the request was authenticated.

## Draft (2026-11-01)

**No contract.** The read entry points' specs are proved and hold in either auth mode
(`E.authMode`), so the handlers take them as callee specs (`EtcdServer__LeaseTimeToLive: @` in
`etc/link-lean-first-v3rpc.txt`), not a `raftLeaseRead` contract discharged afterwards as
`raftKV_of_server[On]`: no new definitions between the handler and the server, and the link is
`gen-link`'s. Translated: `LeaseServer.LeaseTimeToLive`, `LeaseServer.LeaseLeases`; v3rpc now imports
the server's `lease` package (`lease.ErrLeaseNotFound`).

**S1. `leaseTimeToLive`'s contract gives the response's header** (a trusted statement, item 2's;
for the user's approval). Today: `resp ↦ w ∗ ⌜w.Header' ≠ null⌝`, which the docstring reads as "a
fresh response (owned) with a header" but does not state for the header: the handler's
`hdr.fill` writes the header's four id fields, so it needs them. Restated: `resp ↦ w ∗ ⌜w.Header'
≠ null⌝ ∗ ∃ hv, w.Header' ↦ hv`. Faithful: the leader's `leaseTimeToLive` returns
`&pb.LeaseTimeToLiveResponse{Header: &pb.ResponseHeader{Revision: s.KV().Rev()}, …}`
(`v3_server.go`), the follower's the reply `leasehttp.TimeToLiveHTTP` decodes into a fresh message
(its header fresh too; non-nil by the contract's peers assumption).

**S2. `EtcdServer.LeaseTimeToLive.spec`'s post passes it on** (a frozen spec, item 2's): the success
disjunct gains `∃ hv, w.Header' ↦ hv`; the proof passes the contract's on.

**S3. `v3rpc.LeaseServer.LeaseTimeToLive.spec`**: the `*LeaseServer` (`leaseServerAt p s A cid
mid`), the entry point's precondition, and what the header's `fill` needs, `A.revR` (the server's
`srvKVAns` has `mvcc.storeReader E.s E.γ`), all given back; the answer:
- the server's success: `resp ↦ w` with its header filled (`hdrFilled w.Header' cid mid`, a
  revision), `authedOutB`, and if `Keys`, the key check's verdict
  (`leaseCheckFrom … leaseKeysVerdictFrom … .read`), as the entry point's;
- `ErrLeaseNotFound` (`errors.Is`): a fresh response, `ID` the request's, `TTL` `-1`, its header
  filled, and nothing else (the entry point's error post is `applyErrIs`: not even that the caller
  was authenticated, though `requireAuthInfo` runs first in Go; a margin, not a gap a client sees:
  the answer reveals only that the local lessor has no such lease);
- another error: `nil` and `togRPCError`'s non-nil error.

**S4. `v3rpc.LeaseServer.LeaseLeases.spec`**: the same over `EtcdServer.LeaseLeases.spec` (whose
pre already holds `mvcc.storeReader E.s E.γ`; `fill` then needs `A.revR` once more, so the spec
takes `⌜A.revR = mvcc.storeReader E.s E.γ⌝` and one reader); the answer: the listing
(`leasesRespIs`'s ids) with its header filled and the verdict over every id, the empty listing on
`ErrLeaseNotFound` (unreachable: `LeaseLeases` never returns it; kept as Go's code), or an error.

Not in this stage: the quota wrapper's promoted `LeaseTimeToLive`/`LeaseLeases` (the registered
`*quotaLeaseServer`'s, as `LeaseRevoke`'s, `QuotaLeaseLemmas.lean`); the keep-alive (next stage).

## Review (2026-11-01, an independent spec-reviewer) and the redesign

Nine findings; what each changes:
1. **LeaseLeases' header ids**: the spec tied `leaseServerAt`'s `cid mid` (chosen by
   `NewLeaseServer`) to `srvHeaderFacts`' (the server's): no caller can show them equal, and `fill`
   overwrites them anyway. Fixed by the contract shape (below): the server's ids are hidden in the
   contract's answer.
2. **The not-found response carries no authentication**: `ErrLeaseNotFound` comes only from
   `leaseTimeToLive`, after `requireAuthInfo` and the key check, but the entry point's error post is
   `applyErrIs` alone. Stating it needs the error's identity through the chain (that the auth
   errors are not `ErrLeaseNotFound`). Approved at Freeze (2026-11-01) as a margin, stated in the docstrings.
3. **The bounds gate**: the handler specs inherited `threadBound`/`receiptBound` (+3). Fixed by the
   contract shape: the premises go to the discharge theorem, a Proof file.
4. **S1's docstring**: the leader's header is `&pb.ResponseHeader{}` (revision 0, `// TODO: fill out
   ResponseHeader`), not `{Revision: s.KV().Rev()}`; corrected. The collections resting on the
   contract are listed at Freeze (PRINCIPLES: a strengthened axiom in place).
5. **A reachable panic**: a forwarded reply whose response has no `Header` passes `TimeToLiveHTTP`
   and panics in the handler's `fill`. Recorded and reproduced:
   `issues/etcd-leasehttp-timetolive-nil-header-panic.md`.
6. **LeaseLeases drops the revision's certificate** (`srvHeaderAt`'s `idxCert`): kept in its answer.
7. **The not-found responses under-described**: TTL's states `GrantedTTL` `0` and `Keys` nil;
   LeaseLeases' `↦* []`; `leasesRespIs` split (header, listing) instead of copied.
8. **Resources at the dispatch**: the gRPC run slot holds neither `lessorRdOf` nor a thread token;
   open for the stage that links the handlers to the gRPC server (stated in the plan).
9. **`leaseHdrDone` drops the header's other fields**: stated in its docstring.

**The probe's finding** (2026-11-01): Go calls `errors.Is(err, lease.ErrLeaseNotFound)` twice; the
model's `errors.Is` need not answer the same twice, and a `true` then `false` reaches
`fill(resp.Header)` with `resp == nil`. The user (2026-11-01): **a Perennial change**, an
`errors.Is` whose answer is a function of an exact error tree (`notes/perennial-changes.md`, "`errors.Is`
answers the same twice"); the handlers' proofs wait for it.

**The redesign** (the reviewer's recommendation): a contract `raftLeaseRead s E γl S R` (the
server's `LeaseTimeToLive` and `LeaseLeases` at the per-call resources `S` and the KV's revision
reader `R`, which `LeaseLeases` reads and `fill` needs, both given back, quantified over the lower
bounds `n`, `m` and the context), discharged by `raftLeaseRead_of_server` from the two proved specs
(`S := E.RD ∗ lessorRdOf γl ∗ threadTok`, `R := mvcc.storeReader E.s E.γ`; the bounds premises
there); the handler specs over it, as `LeaseGrant`/`LeaseRevoke` over `raftLessor`.

## Probe (2026-11-01): the proofs

Both handlers and the contract's discharge are proved and linked. `LeaseServer__LeaseTimeToLive` and
`LeaseServer__LeaseLeases` are in `etc/link-lean-first-v3rpc.txt` (callees `errors_Is togRPCError
header__fill`), and `raftLeaseRead_server` is in v3rpc's `Results.lean`. The exception is one arm
per handler: the second `errors.Is` answering `false` after the first answered `true` was a `sorry`
until Perennial `c4a24e323` (`notes/perennial-changes.md`, "`errors.Is` answers the same twice");
it is now closed by `isWalk_det` over the exact `applyErrIs` tree (`applyErrIs_walk`).

What the proofs needed:
- `LeaseLeases`' header revision is the server's certified one: `leasesHdrDone` keeps `idxCert` and
  `rev ≠ 0 → r' = rev` (`hdrRevOut` returns no reader when the revision is not `0`, so
  `hdrRev_in`/`hdrRev_out` persist it);
- the empty listing `[]*pb.LeaseStatus{}` is `wp_slice_literal` at `[]`;
- `etc/gen-init.py`'s v3rpc entry names dependency hypotheses by index (`Hd37`, `Hd44`); the
  new `lease` import shifted them.

**For Freeze** (the user's): S1 (the trusted contract strengthened: the collections resting on it,
`etc/tcb-report.py --roots`), S2 (the frozen `EtcdServer.LeaseTimeToLive.spec`'s post), the
`leasesRespIs` split, and the not-found margin (finding 2). `applyErrIs` (exact tree) changed in meaning, not in the specs' text.

**Freeze: approved by the user (2026-11-01)**, all five as proposed: S1 (the trusted
`leaseTimeToLive` contract gives the header), S2 (`EtcdServer.LeaseTimeToLive.spec` passes it on), the
not-found margin (no authentication on the `ErrLeaseNotFound` answer; stated in the docstrings), the
`applyErrIs` exact tree, and the `leasesRespIs` split. Merged into `lean`.
