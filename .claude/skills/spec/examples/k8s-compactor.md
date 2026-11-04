# Kubernetes' etcd compactor: a protocol on a shared key, specified by a caller's contract (2026-11-04)

**Kind:** a client loop (several processes compare-and-swap one etcd key, the winner compacts) whose
safety depends on every writer of the key, over a client whose KV state another invariant owns.

**Approved by the user** as Draft 2 with four decisions (U1-U4), after one `spec-reviewer` round.
The specs: `Spec/k8s_io/apiserver/pkg/storage/etcd3/{Compact,NewCompactor,compactor__*}.lean`; the
shapes: `CompactorDefs.lean`; `notes/decisions.md`, "Kubernetes' compactor: the specs".

## First version (Draft 1)

A contract `casOk` with a caller's `Seen`, and per-member lower bounds `[∧list] x ∈ ms, kvRevLbZ
x.γr.kv rev`. The round's facts were pure (`c ≤ σ.rev`), and the post said "the reported revision
is reached".

## Critiques and what they changed (the reviewer's)

1. **Every premise needs a source.** The contract's result asked the caller for a revision lower
   bound at the commit, but a caller holding only `etcdKV` has no law producing one; the client's
   `Txn` reply gave none, while `Put`'s did. So the bound now comes from the reply, with
   `txn.Commit.spec` strengthened (U1, the user's decision). The recorded value's bound is a
   resource the caller's invariant keeps from the put, not the pure `c ≤ σ.rev`.
2. **A lower bound at a negative revision is trivially true.** One predicate, `revOk r := r = 0 ∨
   (0 < r ∗ kvRevLbZ r)`, everywhere: the first round's `0` and a compaction's `1 ≤ rev` both come
   from it.
3. **A token the spec relies on returning must be persistent if it can be consumed.** `Seen` and
   `recorded` are now `[Persistent]`.
4. **Take what the callee takes.** The client's resources were missing (`clientWriteOnce`, the
   registrations, one cluster name with `kvSame`), as `OptimisticPut` takes them. A cluster-wide
   fact is stated once at the cluster's names, not per member.
5. **Complete for the planned client.** The example checks that a compaction is at a *recorded*
   revision and that `CompactRevision` only grows. Both are now in the specs (`recorded c`,
   `compactRevLb`).
6. **Never strengthen an axiom to something false of Go's default.** "The feature gate answers
   false" is a premise (`gateOff`), produced by a trusted spec of the program's own `Set` call, not
   a stronger init axiom (U3).

## Found while writing the approved Draft 2

`Stop` cannot return the loop's thread token: `sync.Once`'s spec passes out only a persistent result.
So `Stop` returns nothing, and Draft 2's exclusive `stopTok` was dropped. *Lesson:* check what a
library's idiom lets flow out before a spec promises it.

**Principles shown:** every premise has a source a realistic caller can produce; a caller's contract
for a protocol the callee cannot own; a premise in place of an axiom false of the default.
