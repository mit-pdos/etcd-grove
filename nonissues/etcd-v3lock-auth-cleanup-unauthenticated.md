---
upstream: none
checked: 2026-11-09
links:
blocks-proof: no
---
# v3lock/v3election: with auth enabled, a canceled Lock or Campaign leaves its waiter key behind

With auth enabled, the server-side lock and election services (`server/etcdserver/api/v3lock`,
`v3election`) run `client/v3/concurrency` over the in-process client (`v3client.New`), whose
requests carry the principal of the context they are sent with (the RPC's incoming metadata). When
a `Lock` RPC's context is canceled while it waits, `Mutex.Lock` cleans up with
`m.Unlock(client.Ctx())` (`client/v3/concurrency/mutex.go:92,99`), and `Campaign` with
`e.Resign(client.Ctx())` (`election.go:98`): the in-process client's own context, which carries no
token, so the delete is refused as unauthenticated (`ErrUserEmpty`, `auth/store.go`'s
`isOpPermitted`) and the error ignored. The waiter key `name/<lease>` then stays until the remote
client's lease ends, and holds the lock (or leads) for nobody in the meantime.

**Why not an issue:** found by code reading, unconfirmed: no test yet (it needs an auth-enabled
cluster, a v3lock `Lock` that waits behind another holder, and a canceled RPC context).

## Proof

no: the specs of `Mutex.Lock` and `Election.Campaign` state the cleanup's effect as a possible
delete (a refused delete is a step that changes nothing), and the lock's guarantee (the fence) does
not depend on the cleanup; liveness only.

## Notes

- A test: enable auth, user `u` with readwrite on the lock name's prefix; client A takes the lock
  through v3lock; client B's `Lock` waits, its context canceled; then A unlocks: with the bug, B's
  waiter key remains and a third client C's `Lock` blocks until B's lease expires.
- Fix candidates: clean up with the call's context (detached from its cancellation,
  `context.WithoutCancel(ctx)`), keeping its metadata.
- Batch 1d's review (`notes/specs-only/reviews/1d-completeness-1.md`, C5).
