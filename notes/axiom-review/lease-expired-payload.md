# `lease.Lease.expired.wp_proof`: the expiry loop's payload (prove-ps2-newlessor5, 2026-11-21)

**What changed.** `lease.NewLessor.wp_proof` (the whole constructor, an axiom since unit N4, 2026-10-17)
is retired: `NewLessor` is proved over the real code (`Proof/go_etcd_io/etcd/server/v3/lease/NewLessor.lean`
over `newLessor.lean`: the struct, `initAndRecover`, the ghost state at the recovered snapshot
`NewLessorAlloc.lean`/`NewLessorGhost.lean`, `le.mu` made, `go le.runLoop()`, and the backend's contract
`lessorApplyOk_real`, `etcdserver/LessorApplyReal.lean`). The one claim no proof over the model can give is
the payload of `expiredC`: every slice the expiry loop sends carries `¬ leasesNoExpiry`
(`lessorExpiredC`). It now rests on the narrower axiom `lease.Lease.expired.wp_proof`
(`Spec/go_etcd_io/etcd/server/v3/lease/Lease__expired.lean`), the user's choice (a) of prove-ps2-newlessor
(`/shared/tmp/ps2/newlessor/plan.md`, blocker 1). Net trust base: one axiom out, one in.

**The statement.** `{{ isPkgInit lease ∗ isLeaseObj γl l ∗ leaseMeta id l q ∗ levelTok leaseLvl ∗
⌜threadBound GF ≤ 2^30 - 1⌝ }} l.expired() {{ b, RET #b; leaseMeta id l q ∗ levelTok leaseLvl ∗
⌜b = true → ¬ leasesNoExpiry⌝ }}`.

**Why it is true of Go** (`server/lease/lease.go:51-53,117-124`, at the etcd pin):
- `expired()` is `l.Remaining() <= 0`; `Remaining()` read-locks `l.expiryMu` (a slot of the lease's
  `expiryMu` pool, `isLeaseObj`, under the thread bound: as the proved `Remaining.spec`), reads
  `l.expiry` and returns `math.MaxInt64` when it is zero (`forever`), else `time.Until(l.expiry)`. It
  writes nothing; `leaseMeta` (the lessor lock's share) and the level token come back unchanged. No panic:
  the read lock's reader count stays below `2^30` by the pool.
- `true` means the expiry is set and the clock is at or past it: the lease expired while the program
  runs. `leasesNoExpiry` (`LessorBackend.lean`, an opaque premise of the top-level lease theorems) says
  exactly that this never happens to a lease of a lessor the program creates (runs shorter than every
  granted TTL). So `b = true → ¬ leasesNoExpiry` is the premise's meaning, nothing more.
- Stated inside the triple, not as a pure lemma: in the model `time.Now` is arbitrary
  (`Proof/time/Base.lean`), so `expired()` may return `true` in a model run; a pure implication outside
  a triple would let Lean refute `leasesNoExpiry` from the model, the triple only constrains the runs the
  premise allows.

**Attack attempted.** A program whose proof could use the post to derive `False` without the premise: the
post's only non-trivial part is guarded by `b = true`, and `leasesNoExpiry` is opaque (no proof of it or
its negation in Lean), so the axiom is consistent with every model run (take `leasesNoExpiry` false). A
client that assumes `leasesNoExpiry` (the lease theorems) gets `b = false` from every call, which is the
Go behavior under the premise. Survives.

**To retire it**: a Perennial model of `time.Now`'s monotonic reading, with `leasesNoExpiry` restated
over the readings (then this is a lemma of `Remaining`'s proof).
