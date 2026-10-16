# etcd-io/raft#48: Cluster struggles to elect leader when all peers are started at the same time

<https://github.com/etcd-io/raft/issues/48>. The report itself is etcd-io/etcd#15784. Closed
2023-06-29. The fix is etcd-io/raft#50 (merge `7f872e8af`, commit `780bbb2b0`, "change math/rand
to crypto/rand to break tie in elections"). The issue was found in a Shadow simulation, where
simulated time makes processes start at the same nanosecond.

**The bug.** raft's `globalRand` was `rand.New(rand.NewSource(time.Now().UnixNano()))`
(`raft.go`, before `780bbb2b0`). Peers started at the same instant got the same seed, so the
same sequence of `randomizedElectionTimeout`s (`resetRandomizedElectionTimeout`, `raft.go:2045`
at the pin). They campaigned in lockstep and split the vote term after term: up to 36 terms
in the report, instead of about 2. The fix draws from `crypto/rand`.

## Classification

**F−** (fixed before the pin; the spec would admit the buggy version), secondary **C-live**
and **A-model**. The decisive fact: `780bbb2b0` is an ancestor of the raft pin `509271dac`, and
the pin's `lockedRand.Intn` calls `crypto/rand.Int` (`raft.go:97-101`). The old code would still
meet `lockedRand.Intn.spec`, which only says the result is in `[0, n)`. Election progress is
liveness. The model has no clock, and no randomness beyond the range of a draw, so no spec
here can tell correlated timeouts from independent ones.

## The code path and its verification state

Source: `/shared/etcd-grove-triage/coord/verified.txt`, all "verified (sorry-free)":
`lockedRand.Intn` (`raft.go:97`), `raft.resetRandomizedElectionTimeout` (`raft.go:2045`),
`raft.reset`, `raft.tickElection`, `raft.pastElectionTimeout`, `raft.hup`, `raft.campaign`. The
RNG is `crypto/rand.Int`, through Perennial's model: `Spec/crypto/rand/Int.lean`, proved in
`Proof/crypto/rand/Int.lean:26`.

## The counterfactual (step 5)

- `lockedRand.Intn.spec` (`Spec/go_etcd_io/raft/v3/lockedRand__Intn.lean:25-30`) is
  `0 < n → {isPkgInit ∗ isLockedRand lr} lr.Intn(n) {v. 0 ≤ v < n}`. The pre-fix body
  `r.rand.Intn(n)` under the mutex meets it, given a range spec for `math/rand`'s `Rand.Intn`
  (this repository has `Spec/math/rand/Int63n.lean` of the same kind). `isLockedRand` would
  have to own the `*rand.Rand` instead of nothing. That changes the predicate, not what the
  spec says about results.
- `raft.resetRandomizedElectionTimeout.spec` (`raft__resetRandomizedElectionTimeout.lean:34-40`)
  keeps `ownRaftPhysCV c V r id s` unchanged. The header says "the field it writes appears in
  no other conjunct of `ownRaftPhys`, and the model has no clock, so the new value is
  existential". So any timeout values, including identical ones across nodes, meet it.
- The protocol results (election safety, log matching, commit agreement) are safety
  properties and hold for any timing. A run that never elects a leader satisfies all of them.

So the buggy version passes the same proofs: **F−**. The gap is C-live, and the model has no
time or probability (A-model).

## Proposal (step 6)

**`election-liveness-model`** (new, low priority). Leader election terminating with
probability 1 under independent per-node timeouts is a probabilistic liveness theorem. It is
outside Iris partial correctness and would be a pure protocol-level result. It needs a timing
model (rounds or bounded message delay) and an RNG modeled as independent per-node
draws. At the Go level, the only checkable part is the assumption: replace `Intn`'s range spec
with a draw from a ghost per-node random oracle, so the protocol theorem can quote the
independence. No safety property excludes this bug. Cost: large, and needs a Perennial
proposal for a time and probability model. This is related to `lease-clock-model`'s clock, but
a different property.

## Files

None besides this report. The bug is fixed at the pin, so there is no `issues/` file.
