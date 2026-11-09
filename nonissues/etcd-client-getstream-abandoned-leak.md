---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# clientv3: `GetStream`'s reading goroutine blocks forever when its caller stops reading the channel

`KV.GetStream` starts a goroutine that receives the stream's chunks and sends each on a channel of
capacity 1 with a plain send
([`client/v3/kv.go`](https://github.com/etcd-io/etcd/blob/main/client/v3/kv.go), `GetStream`:
`respCh <- RangeStreamResponse{...}`, no `select` on the context). A caller that stops ranging
over the channel after a chunk (Kubernetes' store returns from its list on a decoding error, which
ends its iterator: `k8s.io/apiserver/pkg/storage/etcd3/store.go`, `GetList`) leaves the goroutine
blocked on the next send for good, even once the caller cancels its context: the gRPC stream is
torn down, but the goroutine is stuck on the channel, not on `Recv`. Each abandoned stream leaks one
goroutine and the chunk it holds.

**Why not an issue:** no test; found by code reading (the client's spec review, 2026-11-09). A test
could promote it: a stream of at least two chunks over an integration cluster, the consumer reading
one chunk, cancelling its context and returning, then `goleak` (or a goroutine count) after a grace
period.

## Proof

no: a leaked goroutine is a liveness and resource defect; the client's `GetStream` spec gives the
caller's thread token to the goroutine and returns it only for a drained stream
(`Spec/go_etcd_io/etcd/client/v3/kv__GetStream.lean`, its margin), so a proof that bounds threads
(Kubernetes' store) must drain every stream it opens or account for the lost token.

## Notes

Fix: send with `select { case respCh <- r: case <-ctx.Done(): return }`, so a consumer that cancels
its context releases the goroutine.
