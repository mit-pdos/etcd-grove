# The gRPC lease keep-alive stream (item 6, second stage, 2026-11-01)

`v3rpc/lease.go`'s `LeaseServer.LeaseKeepAlive`: runs `leaseKeepAlive(stream)` on a goroutine, a
loop that receives a request, fills a response header, renews through the server
(`ls.le.LeaseRenew`, `ErrLeaseNotFound` turned into TTL `0`) and sends the response. The full design
is `notes/lease-keepalive-plan.md`.

## The first version

The stream's specification `Dn` named the run's bounds `n`, `m` (the auth store's published index,
the lessor's history index) and the run's context; the server read the client's messages through a
second wire model of its own; the handlers took the unary reads' contract `raftLeaseRead … S` with
the renewal added at the same `S`; `NewServer` was to export `peerRt` alone.

## The review and what it changed

1. **Unregistrable** (reviewer): a stream's spec is fixed when the service registers, indexed by
   metadata only, so it cannot name a run's bounds or context. Fixed: `Dn` over the run's token
   (`leaseCheckT … (auth.ctxTokenOf (ok ci))`, as watch's `watchAuthed`), and the bounds per request,
   as ghost fields of the request's model (`KaReqM.nb`, `.mb`, as watch's create `bound`), vouched for
   by the client's content `Up` (`kaUpOk`).
2. **Two wire models** for one message: the client's and the server's must be the same trusted
   statement. Fixed: `LeaseKeepAliveMsg.lean`, shared by both ends.
3. **Shared resources widened**: the renewal needs reader slots the unary reads do not use. Fixed:
   its own contract `raftLeaseRenew … S'`.
4. **An export that closes nothing**: `peerRt` alone left the discharge's other premises without a
   source. The user chose to export the lease facts from `NewServer` (`srvPeerRt`, `srvLessorRd`)
   and to derive `srvHeaderFacts` by a law from `isServerReqM` instead of exporting it.
5. Smaller: the loop logs, so `leaseServerAt` needs the logger; the loop gives back its per-call
   resources; the margins stated (a TTL of `0` carries nothing; the verdict is the local lessor's;
   a failed `Send` may have delivered). A claim in a Go comment (the header's revision no later than
   the renewal's) was checked in the code, not assumed: it holds.

## Approved

The user approved K2-K6 with the margins, and K7 (`bootOk` states `prt` a `*http.Transport`;
`NewServer`'s three forms export `srvPeerRt` and `srvLessorRd`), without further critique. The specs:
`Spec/.../v3rpc/LeaseServer__LeaseKeepAlive.lean`, `LeaseServer__leaseKeepAlive.lean`, over
`Proof/.../v3rpc/InvLeaseKeepAlive.lean`.
