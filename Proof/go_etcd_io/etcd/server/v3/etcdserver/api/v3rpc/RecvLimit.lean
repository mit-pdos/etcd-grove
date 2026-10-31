/-
**The receive limit of etcd's gRPC server, and the receive-size fact** (2026-10-30;
`notes/decisions.md`, "The receive-size fact"; `notes/invoke-size.md`, "Receive-size fact").
Lean-first (no Rocq counterpart).

etcd's gRPC server is built by `v3rpc.Server` (`server/etcdserver/api/v3rpc/grpc.go`) with
`grpc.MaxRecvMsgSize(int(s.Cfg.MaxRequestBytesWithOverhead()))`, that is `MaxRequestBytes +
grpcOverheadBytes` (`server/config/config.go`). grpc (v1.84, `rpc_util.go`) receives a request
through `recvAndDecompress`: `parser.recvMsg` refuses a frame whose length exceeds the limit before
reading it, and `decompress` refuses a decompressed message longer than the limit; only then does
the codec (`v3rpc.codec`, `proto.Unmarshal`) decode the bytes into the request. A `bytes` field of
the decoded request holds bytes of that message, so it is at most the limit long. The handlers the
Lock and Election services register on that server (`embed/serve.go`: `RegisterLockServer(gs,
servLock)`, `RegisterElectionServer(gs, servElection)`; the gRPC gateway reaches them through a
client connection to the same server) receive only such requests.

The fact is stated over the length of each `bytes` field (`grpcRecvBytesOk`), not over the
message's encoded size: `ProtoMsg.wireLen` is an upper bound on the encoding (its `wireSlack` per
node), so `wireLen ≤ limit` would be false of a request that fits.
-/
module

public import Perennial.Std.ByteString

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

/-- etcd's `grpcOverheadBytes` (`server/config/config.go`, `512 * 1024`): the room the server's
receive limit leaves above `MaxRequestBytes`. -/
def grpcOverheadBytes : Nat := 512 * 1024

/-- **The receive limit of etcd's gRPC server whose configuration's `MaxRequestBytes` is
`maxReq`**: `v3rpc.Server` builds it with `grpc.MaxRecvMsgSize(int(MaxRequestBytesWithOverhead()))`
(`MaxRequestBytes + grpcOverheadBytes`). This is the limit when the embedding passes no
`grpc.MaxRecvMsgSize` of its own in `Config.GRPCAdditionalServerOptions` (the default: none), which
`v3rpc.Server` appends after etcd's options, so that a later one would replace it. -/
def etcdMaxRecvMsgSize (maxReq : Nat) : Nat := maxReq + grpcOverheadBytes

/-- **etcd's server configuration premise on `MaxRequestBytes`**: the server's receive limit is
below `2 ^ 27` (`MaxRequestBytes` below 127.5 MiB). True at the default
(`embed.DefaultMaxRequestBytes`, 1.5 MiB: `etcdMaxRequestBytesOk_default`); etcd warns above
10 MiB (`recommendedMaxRequestBytes`). It is what the Lock and Election servers need: the prefixes
and values they hand `concurrency` stay within its bounds. -/
def etcdMaxRequestBytesOk (maxReq : Nat) : Prop := etcdMaxRecvMsgSize maxReq < 2 ^ 27

/-- etcd's default `MaxRequestBytes` (1.5 MiB) meets the premise. -/
theorem etcdMaxRequestBytesOk_default : etcdMaxRequestBytesOk (3 * 2 ^ 19) := by
  unfold etcdMaxRequestBytesOk etcdMaxRecvMsgSize grpcOverheadBytes; omega

/-- **The receive-size fact** (trusted: what grpc's server does, see the file header): a `bytes`
field `b` of a request grpc's server decoded under the receive limit `lim` is at most `lim` bytes
long. Stated in the request predicates of the handlers that need it (the Lock and Election
servers' specs), where grpc's runtime is the caller. -/
def grpcRecvBytesOk (lim : Nat) (b : GoString) : Prop := b.length ≤ lim

/-- Under the configuration premise, a received field is shorter than `2 ^ 27`. -/
theorem grpcRecvBytesOk.lt {maxReq : Nat} {b : GoString} (hcfg : etcdMaxRequestBytesOk maxReq)
    (h : grpcRecvBytesOk (etcdMaxRecvMsgSize maxReq) b) : b.length < 2 ^ 27 := by
  unfold etcdMaxRequestBytesOk at hcfg; unfold grpcRecvBytesOk at h; omega

/-- **A transaction budget whose checked transactions fit protobuf's recursion limit** (2026-10-31;
`issues/etcd-txn-nested-depth-apply-panic.md`, `notes/irr-depth.md`): `checkTxnRequest` at the
budget `n` admits a transaction `2n + 1` messages deep (`txnCheck_msgDepth`, tight: a chain of `n`
one-operation transactions over a put), whose `InternalRaftRequest` is `2n + 2`; it decodes at
apply iff `2n + 2 ≤ 10000`. A scope restriction: etcd accepts any `--max-txn-ops`, and from 5000 on
one request takes every member down. A negative budget (`int(maxTxnOps)` of a `uint` at least
`2^63`) refuses every transaction and meets it. etcd's default (128) meets it. -/
def maxTxnOpsOk (n : Int) : Prop := n ≤ 4999

/-- etcd's default `MaxTxnOps` (128) meets the bound. -/
theorem maxTxnOpsOk_default : maxTxnOpsOk (sint.Z (W64 128)) := by
  unfold maxTxnOpsOk; decide

end v3rpc
end EtcdGrove
end Perennial
