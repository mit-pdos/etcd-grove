---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#22082 issue open: this bug (a stale Unlock retry deletes a newer same-session incarnation of the key)
  - etcd-io/etcd#22115 pr open: fences Unlock's delete with IsOwner(); does not change TryLock's delete or the v3lock Unlock RPC
  - etcd-io/etcd#22384 pr open: ResumeMutex, which makes a stale (key, revision) pair easier to reach (notes/pr-verify/etcd-22384.md, finding 3)
---

# concurrency: Mutex.Unlock (and TryLock's cleanup) delete the lock key by name, not by incarnation

## Status

A bug: `Mutex.Unlock` can delete a lock key that a later acquisition holds, so a stale `Unlock`
releases a lock its `Mutex` no longer owns. Reported upstream as etcd-io/etcd#22082 by someone
else; etcd-io/etcd#22115 fixes `Unlock`. The same unfenced delete remains in `TryLock`'s cleanup
path and in the server's `v3lock` `Unlock` RPC.

## Where

`client/v3/concurrency/mutex.go` at the pinned `09669450f`:

- `Unlock`, line 144: `client.KV.Delete(ctx, m.myKey)`, by key name only.
- `TryLock`, line 65: the same delete when the mutex is not the owner ("Cannot lock, so delete the
  key").

`server/etcdserver/api/v3lock/lock.go` line 53: `Unlock` deletes `req.Key`; `UnlockRequest` has no
revision to fence with.

The key name is `pfx/<lease hex>`, the same for every `Mutex` of one session and prefix, so a key
deleted and re-created under the same session is a new incarnation with the same name and a newer
create revision.

## What happens

1. If `Unlock`'s delete commits but the client gets an error (a lost response, `DeadlineExceeded`),
   the `Mutex` keeps `myKey` and `myRev`. A later `Mutex` on the same session and prefix locks
   again and re-creates the key at a newer create revision. Retrying the old `Unlock` deletes the
   new incarnation, releasing the later holder's lock. Reproduction: the PR's
   `TestMutexStaleUnlockDoesNotDeleteSameSessionRelock`
   (`tests/integration/clientv3/concurrency/mutex_test.go` at etcd-io/etcd#22115's head
   `06eca942c`), which fails at the upstream base `6006f4058` with the newer key deleted
   (`notes/pr-verify/etcd-22115/up-base.log`, on branch `pr-verify/etcd-22115`).
2. `TryLock`'s cleanup has the same flaw: if, between its transaction and its delete, the key is
   deleted and re-created by another `Mutex` of the same session, the delete removes the new
   incarnation, and that mutex's waiting `Lock` returns `ErrSessionExpired`.
   `TestProbeTryLockDeleteUnfenced` (`notes/pr-verify/etcd-22115/mutex_trylock_unfenced_probe_test.go`
   on branch `pr-verify/etcd-22115`) shows it at the PR head; the window is narrow, and it needs
   another handle on the same session.

## Expected

A `Mutex` releases only the incarnation it acquired: `CreateRevision(myKey) == myRev`, the
comparison `IsOwner()` already builds (and that `Election.Resign` already uses for its key).

## How the proof handles it

On `lean`, `Mutex.Unlock`'s spec (`Spec/go_etcd_io/etcd/client/v3/concurrency/Mutex__Unlock.lean`)
says only that on `nil` the key is absent at some revision (`etcdAbsent`), whatever incarnation was
there. That is true of the unfenced delete, which deletes the newer incarnation. No triple over
the client's model can exclude the bug: the model records knowledge of etcd's states only, so a
delete made by the call cannot be told apart from another client's delete at the same revision
(`notes/decisions.md` on branch `pr-verify/etcd-22115`, "Unlock's fence and the knowledge-only
client model"). On that branch the fence is proved about the transaction `Unlock` commits:
`mutex_unlock_txn_fenced` against `mutex_unlock_old_txn_unfenced`
(`Proof/go_etcd_io/etcd/client/v3/concurrency/Results.lean`). `TryLock`'s spec says nothing about
its cleanup delete beyond `ErrLocked`.

## Possible fixes

- `Unlock`: etcd-io/etcd#22115, `Txn(ctx).If(m.IsOwner()).Then(OpDelete(m.myKey)).Commit()`.
- `TryLock`: the same fence on its cleanup delete.
- `v3lock`: an `UnlockRequest` that carries the key's create revision (an API change), or a
  documented caveat.

## Found

2026-10-17, while verifying etcd-io/etcd#22115 against the `Mutex` proofs (`pr-verify/etcd-22115`).
