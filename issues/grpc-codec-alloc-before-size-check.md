---
upstream: none
checked: 2026-10-31
links:
  - grpc/grpc-go#9056 issue closed: the same panic message (makeslice: len out of range) from a message mutated while marshaled; not this bug
candidate: issues/upstream/grpc-codec-alloc-before-size-check/
---

# grpc-go: the codec allocates a message's full encoded size before the send-size check, so a huge request panics instead of failing with ResourceExhausted

- **Status**: bug (a reachable panic in the client, instead of the documented error). Found by the
  axiom review of the nested-transaction wire model (`notes/axiom-review/txn-nested-wire.md`), which
  refuted `grpc.ClientConn.Invoke`'s send side.
- **Where** (grpc-go v1.84, the version etcd's pin uses): `encoding/proto`'s `codecV2.Marshal`
  allocates `proto.Size(m)` bytes (rounded up to 4 KiB) before `encode`'s `MaxUint32` check and
  `SendMsg`'s `MaxCallSendMsgSize` check. Go panics with `makeslice: len out of range` when the
  allocation exceeds `maxAlloc` (2^48 on 64-bit).
- **What happens**: a message whose encoding is that large needs far less memory if submessages are
  shared. For example, a `TxnRequest` holding `2^18 + 1` references to one get of a `2^30`-byte key
  needs about 2 GiB. `cli.Txn(ctx).Then(ops...).Commit()` panics in the client, where the documented
  behavior is a `ResourceExhausted` error.
- **Reproduction**: `examples/axiomcx/txnwire`'s `TestAttackClientAPI` (and `TestAttack`, through
  `kVClient.Txn`) on branch `axiom/txn-nested-wire`.
- **Fix**: check the size against the send limit before allocating, or cap the allocation and let
  `MarshalAppend` grow the buffer.
- **In the proof**: the generic encoded-size premise on `Invoke`'s and `NewStream`'s send side
  (`grpcInvokerOk`'s pre takes `Req.wireLen ≤ grpcMsgMax`, `grpcMsgMax = 2^32`; landed 2026-10-30,
  `notes/invoke-size.md`) excludes these messages: the client's callers bound their keys, values and
  operations (`txnSizeOk`, ...).
- **Related**: [etcd-txn-keysonly-reply-alloc-panic](etcd-txn-keysonly-reply-alloc-panic.md) is the
  same codec allocation panic on the **server** reply side, reachable from etcd through a `Txn` of
  nested keys-only whole-range reads (whose reply aliases the index's key slices); the server reply
  side is still known-false in the proof (`notes/audit.md:338`).
