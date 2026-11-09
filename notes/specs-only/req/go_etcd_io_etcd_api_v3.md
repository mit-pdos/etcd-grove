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
