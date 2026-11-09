# Requirements on the client-observable model and state (`Spec/go_etcd_io/etcd/api/v3/`, batch W0)

## from 1f

1. **The current revision with one to spare**: `etcdState_revFits` gives `σ.kv.rev < 2^63`; the
   recipes compute `resp.Header.Revision + 1` in `int64` (`Barrier.Wait`'s watch start,
   `newSequentialKV`'s guard), which wraps at `2^63 - 1`. Wanted: `σ.kv.rev + 1 < 2^63` (the
   adequacy theorem's step bound gives any margin).
   ```go
   _, err = WaitEvents(b.client, b.key, resp.Header.Revision+1, []mvccpb.Event_EventType{mvccpb.Event_DELETE})
   ```
   Used by: `Barrier.Wait.spec`, `newSequentialKV.spec` (their sketches).

2. **The cluster's states are well formed**: a law giving that every state the cluster has been in
   is reachable from an initial one (`etcdLb γ σ ⊢ ⌜∃ ms, Reach (State.init ms) σ⌝`), or the
   facts it implies stated as one well-formedness predicate: a present key has version `≥ 1` and
   create revision `≤` mod revision `≤ rev`, and its mod revision is the revision of the event that
   wrote its record. Without it a recipe that reads `σ0` cannot conclude that `Version(k) = 0`
   means `k` is absent (`putNewReq`: the created record is a first version, `createdAt`), nor that
   a key present at a later state with a mod revision `≤ σ0.kv.rev` was present at `σ0`
   (`frontByRev`, `frontByKey`: the queues' front at the claim).
   Used by: `Queue.Dequeue.spec`, `PriorityQueue.Dequeue.spec`, `DoubleBarrier.Enter.spec`
   (`createdAt`), `RWMutex.Lock`/`RLock.spec` (the key's revision).
   (The same holds of 1d's `Mutex` sketches: a client proving a pure fact of the model from an
   `etcdLb` needs the state's provenance.)

## from 1b

1. **The watch messages belong with the KV ones** (`Wire.lean`): 1b defined, in
   `Spec/go_etcd_io/etcd/client/v3/ApiWatch.lean`, the models `EventM` (`mvccpb.Event`),
   `WireWatchRespM` (`pb.WatchResponse`), `WireWatchReq` (`pb.WatchRequest`'s create, cancel and
   progress), with `eventOwn` (and `eventOwn_unfold`), `wireWatchRespOwn`, `watchReqOwn`; 2b builds
   them, so they would be better in `api/v3/Wire.lean` (or a `WireWatch.lean` next to it). If W0
   moves them, 1b's files only change their import. 1b did not edit W0's files.
2. **A compaction retention in the environment's configuration** (`EnvCfg`): `examples/etcd/
   compactwatch/compactkv.go:142` panics unless `Get.rev ≥ CompactRevision + retention`; the
   watch's compaction fact (`CompactRevision ≤ σ.kv.compacted`) gives the bound only if the model's
   auto-compaction step keeps `compacted ≤ rev - retention` (`EnvStep.compact`'s `r ≤ σ.kv.rev`
   allows any). Not needed by any other watch user; a question for W0's model (and the user).
3. **A pure fact clients need, theirs to prove** (no request, noted for the reviewers): `Reach σ σ'`
   keeps the history a prefix (`σ.kv.revs <+: σ'.kv.revs`) and the compaction revision monotone;
   every watch consumer reads `watchStep`'s facts at `σ` against its own later state through it.

## from 1d

1. **The cluster's states are well formed** (the same request as 1f's item 2): `etcdLb_init :
   etcdLb γ σ ⊢ ⌜∃ ms, Reach (State.init ms) σ⌝`. 1d's sketches use it for: a present key has a
   create revision `≥ 2` and a mod revision `≥ 2` (so `CreateRevision(k) = 0` and
   `ModRevision(k) = 0` mean `k` is absent: the mutex's and election's create-if-absent
   transaction, the STM's `isKeyCurrent` of an absent key); `Mutex.Lock`'s `myRev - 1 > 0`
   (`waitDeletes`' filter is off at `0`).
   ```go
   cmp := v3.Compare(v3.CreateRevision(m.myKey), "=", 0)
   werr := waitDeletes(ctx, client, m.pfx, m.myRev-1)
   ```
   Used by: `Mutex.tryAcquire.spec`, `Mutex.Lock.spec`, `Election.Campaign.spec`,
   `stm.commit.spec`, `stmSerializable.commit.spec`.

## from 1g

1. **The read permission `etcdPeek γ`** (1f's definition, `client/v3/experimental/recipes/Api.lean`):
   the cache defines the same body (`Cache.etcdPeek`) for `New`'s precondition (its background list
   and the revision a linearizable `Get` waits for are client `Get`s that need a persistent update).
   Wanted: one definition in `State.lean`, which both batches then cite.
   ```go
   resp, err := c.kv.Get(ctx, c.prefix, clientv3.WithPrefix())   // the cache's own read
   ```
   Used by: `New.spec`, `Cache.get.spec`, `Cache.serverRevision.spec`.
2. **Revisions only grow** (`Reach σ σ' → σ.kv.rev ≤ σ'.kv.rev`, a pure lemma the cache proves
   itself; noted, no request): `Cache.serverRevision.spec`'s `σ0.kv.rev ≤ σ1.kv.rev`.
4. (1b, round 1) **A bound law on reached states**: `etcdLb γ σ ⊢ ⌜σ.kv.rev < 2^63 ∧
   σ.kv.compacted ≤ σ.kv.rev⌝`, so that a watch consumer without the owner's invariant (Kubernetes'
   watcher) can compare revisions it reads (`etcdState_revFits` gives it only at the current state).
   (Update: W0's round 2 added `etcdLb_revFits`; the `compacted ≤ rev` half follows from the
   model, a pure lemma of the client.)
