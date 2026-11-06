# `EtcdServer.ensureLeadership` with a level token (revoke-open Q5): survives (2026-11-06)

**Reviewed.**
- The axiom `EtcdServer.ensureLeadership.wp_proof`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__ensureLeadership.lean:26`), its triple in
  `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__ensureLeadership.lean`, as restated on branch
  `revoke-open` at `c4c73affdc` (Q5 (a) of `notes/revoke-open-plan.md`):
  ```
  ∀ s E ρ γr (l : Nat),
  {{ isPkgInit etcdserver ∗ isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗
     srvLgReader s ∗ srvReadReader s γr ∗ levelTok l ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ }}
    s.ensureLeadership()
  {{ (b : Bool), RET #b; srvLgReader s ∗ srvReadReader s γr ∗ levelTok l }}
  ```
  On `lean` the token is a whole `threadTok`, in the pre and the post; nothing else changed (the diff
  is the binder `l`, the token and the docstring).
- Perennial's level tokens at `/shared/perennial-84d538063` (`84d538063`, branch `thread-levels`):
  `Perennial/GooseLang/Threads.lean` (`levelKey`, `levelTokList`, `levelToks`, `levelTok`,
  `threadTokFrom`, `threadToks`, `levelToks_lt`, `threadTok_level0`, `threadTokFrom_succ`),
  `Perennial/Proof/sync/RWMutexThreads.lean` (the leveled reader pools), `GooseLang/BoundedLang.lean`
  (`RealThreadsBelow`: `threads < T` along the executions adequacy is about).
- Its uses: `EtcdServer__LeaseRenew.lean:402-406` (level 0: `threadTok_level0` split, the call, the
  token rejoined); the revocation's outer goroutine at level 3 (`RevokeCtx.lean`'s table; its proof is
  still a draft at `c4c73affdc`, not yet linked).
- etcd at the pin of `etc/goose.py` (the fork's `673da07c8`, clone `.lake/goose/etcd` of
  `/shared/etcd-grove-leaseexp`). Line numbers below are at `673da07c8`.
- No earlier review: `notes/axiom-review/` had no report on this axiom and `notes/audit.md` no row
  (the axiom dates from the lease-renew plan's C2, 2026-11-01, after the audit's phase A).

**Verdict: survives.** The token is a frame: the axiom takes `levelTok l` and gives back the same
`levelTok l`, and the Go body never needs it. So the restated triple follows, by the frame rule, from
the same triple with no token at all (Q5's option (b)), and is weaker than that one. The tokenless
triple is true for the reason the docstring gives: the only lock the body takes without a slot is
`r.tickMu`, and its readers are goroutines inside `getLatestTickTs`, fewer than `threadBound GF`,
which is below Go's reader limit. That argument never used the token, as Q5 said. A level token
cannot be turned into more than it was: the post returns the one the pre took, at the same level, and
no fact about its slot or level. No counterexample, and no `issues/` finding.

## The claims

1. **No panic, for any server the facts describe.** The body logs, reads the tick time under
   `tickMu`'s read lock, makes a timeout context, waits for a linearizable read, and compares
   `raftStatus().Lead` with the member id.
2. **The two reader slots come back.** `Logger()` releases `lgMu`, and `LinearizableReadNotify`
   releases `read.mux`, before `ensureLeadership` returns.
3. **`tickMu`'s read locks need no slot from the caller.** Go cannot overflow their reader counter
   while `threadBound GF ≤ 2^30 - 1`.
4. **The caller's level token comes back unchanged.** This is the new claim. Every `l` is allowed,
   so the caller chooses the level.
5. **Any boolean.** The result claims nothing about leadership, so there is no wrong result to find.

## The Go code (`server/etcdserver/server.go`, `raft.go`)

- `ensureLeadership` (917-944): `lg := s.Logger()` (448-453: `lgMu.RLock`, read `s.lg`, `RUnlock`);
  `s.isActive()` (910-914: `s.r.getLatestTickTs()`, 3 ticks, `time.Now()`); if active, `lg.Debug(…,
  zap.Time(s.r.getLatestTickTs()), …)` and `true`; else `context.WithTimeout(s.ctx,
  s.Cfg.ReqTimeout())`, `defer cancel()`, `s.read.LinearizableReadNotify(ctx)` (error: `Warn`, `false`),
  `s.raftStatus().Lead` (2475: `s.r.Node.Status()`) against `s.MemberID()`.
- `getLatestTickTs` (`raft.go:169-173`): `tickMu.RLock(); defer RUnlock()`. The lock's only writer is
  `tick` (`raft.go:162-167`, raft's goroutine). `getLatestTickTs` is called only from `isActive` and
  `ensureLeadership` (`git grep` at the pin). `ensureLeadership` has three callers: the lease
  checkpointer (`server.go:400`), `revokeExpiredLeases`'s goroutine (869) and `LeaseRenew`
  (`v3_server.go:503`).
- `lgMu` is only ever read-locked (448-451 are its only uses), so the slot is all `Logger()` needs.

## The attacks

1. **The level arithmetic: `l ≥ threadBound`.** For `l ≥ T`, `levelTok l` holds the ghost key
   `levelKey l k = l*T + k` with `k + 1 < T`. That key is above every key `thread_init` allocates
   (levels `< T`), and without the map's authoritative part no key can be made. So the precondition is
   unsatisfiable there, and the axiom says nothing. Even if such a token could be made for free, the
   triple would still be true, because the tokenless form is true.
   For `l < T`, the keys of different levels never collide (`k < T`). The axiom returns the token it
   took, so it neither mints nor merges tokens. The axiom is no source of `levelTok l`, and no other
   level comes out of it. **Fails**: the token is never consumed or produced.
2. **The read-slot argument: other holders collect every reader slot.** `srvLgReader s` and
   `srvReadReader s γr` are exclusive Perennial `RWMutex` reader tokens (`InvApplier.lean:323`,
   `InvRead.lean:158`). They are in the pre and come back in the post, as before Q5. If other threads
   hold every slot (say, borrowed from the level-1 `raftPool` or the level-2 pool `B` of
   `RevokeCtx.lean`), then a caller cannot meet the precondition, which is safe. The axiom never makes
   a slot. In Go, the two locks are released before the return (claim 2). `LinearizableReadNotify`'s
   proved spec (`read/Read__LinearizableReadNotify.lean`) takes and returns `readReader` and needs no
   thread token. **Fails.**
3. **`tickMu`'s readers, with level tokens instead of whole ones.** This attack asks whether level
   tokens let more goroutines into `getLatestTickTs` than whole tokens did. A WP runs in a model
   thread, and each thread runs one call at a time, so a level token adds no concurrent reader: the
   readers are at most the live threads, whatever tokens they hold. That count is
   `threads < T ≤ 2^30 - 1` (`RealThreadsBelow`). The writer, raft's goroutine, is one of those
   threads, so at most `2^30 - 3` threads can be readers.
   Go fails only from `2^30` concurrent readers with a pending writer. `Lock` subtracts
   `rwmutexMaxReaders = 2^30`, and an `RUnlock` that then sees `r + 1 == 0` throws "sync: RUnlock of
   unlocked RWMutex".
   One reader may be a goroutine the model does not show: the lease checkpointer, if the lessor's
   loop is outside the model. That adds one reader, still below the limit. Holding several levels of
   one token does not let one thread be several readers. The revocation's outer goroutines "overlap
   without bound" (`RevokeCtx.lean`), but each is a `GoAttach`ed model thread, so each counts towards
   `T`. **Fails.**
4. **Callees that need a whole token.** If a callee's proved spec took a `threadTok`, a caller with
   only `levelTok l` would get a triple that the body's own proof could not give. None does:
   - `context.WithTimeout` (Perennial `Spec/context/WithTimeout.lean`) takes `isContext` only;
   - `node.Status` (`Spec/go_etcd_io/raft/v3/node__Status.lean`) takes `isNode` only;
   - `read.LinearizableReadNotify` takes `readReader` only;
   - zap's specs and `time.Now` take no token.

   `WithTimeout` parents on `s.ctx`, a `cancelCtx`, so `propagateCancel` starts no goroutine. The
   timer's `AfterFunc` goroutine never touches `tickMu`. **Fails.**
5. **Strength against the old axiom.** The new axiom implies the old one: frame `threadTokFrom 1`
   through `threadTok_level0`. So it is stronger, and that is why it needed this review. It is also
   weaker than the tokenless triple, whose truth is attack 3. **No gap.**
6. **A wrong result, or a deadlock that gives one.** The post claims any `b`, so there is nothing for a
   wrong result to contradict. A deadlock (`LinearizableReadNotify` until the timeout, `Status` once
   the node has stopped: raft v3.7's `Status` returns `Status{}` on `n.done`) is not a counterexample
   under partial correctness. **Not applicable.**

**Not tried, and outside Q5.** The premises `isServerReqM`/`isServerReadM` and a nil `s.lg` were not
re-attacked: Q5 did not change them, and `LeaseRenew` reaches the axiom with a live server. The
correspondence between real goroutines and model threads was not re-examined either. It matters when
a names-only axiom runs real goroutines that call back into the code without a model fork. That is a
property of every thread-bound argument, Q5 did not change it, and attack 3 relies on it as the old
axiom did.
