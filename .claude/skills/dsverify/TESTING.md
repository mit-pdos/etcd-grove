# The executable top-level test

In a challenge this program is **given**: it is what the goal is about (`CHALLENGE.md`), and you do
not change it. This file says what it is, why its shape makes the theorem strong, how to run it as a
test, and what you prove about its model. Run it before any spec.

## The shape: a deployment that panics unless the history is consistent

The kit's Go module (`examples/dsverify/<kit>/`), its kit package's machines, each a program of its
own (`cmd/<machine>/main.go`) on a machine of its own, over TCP (`NET.md`):

1. **Server machines** run the target's real code, connected through its real transport.
2. **Client machines**, one per client, each run their own client of the target through its real
   client API (`remote.ServeClient`): a few operations per client is enough for the proof (the
   theorem quantifies over all schedules).
3. **The driver** chooses the configuration (at random: below), drives the clients' operations
   through `remote.Do`, **records the history** (lintest, with a logical clock: a counter under a
   lock, what the proof can model, and sound for porcupine since only real-time order matters),
   and **checks it with porcupine** against a sequential model of the service (`remote.Check`),
   **panicking if it is not linearizable**. This is the only check in the deployment: the protocol's
   own invariants are checked in the stress test (below), not in the theorem.

Why this shape: in Perennial, a proof that no machine panics or gets stuck (`Robust`, `NET.md`)
means *every* execution, under every
schedule and every behavior of the environment the axioms allow, produces a linearizable history. That
reading does not rest on trusting porcupine: to get past `Check`, the proof has to establish what
`Check`'s spec requires, and that spec (porcupine's answer on such a history) is proved in the
environment. The test and the theorem are the same program, so the statement cannot drift from
what the system is meant to do, and anyone can run it.

## Making the theorem strong

The theorem is as strong as the test: it covers every execution of *this* deployment, nothing more.
The challenge chose the test; this section is how to read it (`SPEC-FIRST.md`, "Scope") and what to
expect of its proof.

- **One test that covers the protocol.** Test the protocol as its paper or documentation says to run
  it: the configuration it recommends (for example an adaptive leader choice rather than a fixed
  order), and the paths it counts as part of the protocol (recovery, view change, reconfiguration,
  leader change). Not a narrow first test with the rest left for later.
- **Choose the configuration at random, through the model of randomness.** Every parameter whose
  values the protocol supports (the number of replicas, modes, pipeline depth, batch or epoch sizes,
  timeouts) is chosen by the driver with `rand.Intn` (or the like) over its supported range. Proved over a
  model in which `Intn(n)` returns *any* value in `[0, n)`, one theorem then covers every choice. The
  node list stays fixed: deploy the largest configuration's nodes, and let the nodes a smaller choice
  does not use idle. When nodes are separate programs, they learn the choice over the network (one
  writer, a fixed message), never through shared memory.
- **Every source of randomness goes through that model**, never a fixed seed or a concrete value the
  proof could depend on (a coin, a priority, a jitter, a randomized backoff). A property proved over
  the model then holds for every sequence of values.
- **Leave timing to the proof.** Time is not modeled: every timeout may fire at any moment and every
  delay is a schedule, so timeouts and sleeps need no particular values for the theorem. Choose them
  (at random, as above) for the tests' sake.
- **Size the workload to reach the paths that matter.** A few clients and operations suffice for
  the proof of a path the program can reach, but the workload must make it reachable: run past the
  warm-up an adaptive mechanism needs, long enough for a recovery's grace period, with enough
  operations for a leader to change. Show in the tests that each such path is reached (coverage, or
  counts of runs that take it).
- **No adversary in the deployment when the environment's model already has the faults.** Over a network
  model in which connections may break, dials fail and messages wait, partitions and slow links are
  already executions; a thread that injects them adds nothing to the theorem. (An in-process network
  without faults of its own needs the adversary, and then the theorem covers only what it can do.)
- **Say what the theorem leaves out**: liveness, crashes and restarts unless the model has them, the
  bounded workload, any configuration outside the random ranges.

## The sequential model

Written twice:

- **In Go** (given, in the kit package), as a `porcupine.Model{Init, Step, Equal, DescribeOperation}`
  (or `Partition` for a key-value model checked per key), with total, deterministic `Step` and plain
  inputs and outputs.
- **In Lean**, as the pure specification the service's specs are written against (a state, a step
  function, the response): yours to write, unless the challenge gives it, by reading the Go one.

Porcupine is verified in this environment: `remote.Check`'s spec (`NET.md`) is proved, and what it
requires of the kit is that the Go model refines a Lean model spec (`isModel S m`), the codec is
correct (`codecOk`), and the far side's store is the model's (`PendDec`, `pendCtx`). Porcupine's cache
merges only states the model's `Equal` identifies, so `Equal` must be exact equality of the model's
states; a model that violates this is a finding about the challenge.

## Proving the Go model refines the Lean model

Porcupine runs the **Go** model; the theorem is about the **Lean** one. Nothing ties them unless it is
proved, and a Go `Step` that differs from the Lean step (a missed case, a wrong default for an absent
key) makes the top-level theorem say nothing about the service. Do this after Scope fixes the model
and before the interface, as the first linked result:

- The Go model is in the kit's Go module, translated like the target.
- Prove, per function, a **pure spec**: `Step`'s WP returns the Go encoding of `stepL s i`, for every
  state and input encoded as the Go values (`Partition` and `Equal` likewise; `DescribeOperation` needs
  no spec). Write the encoding (Lean value → Go value) once and use it in the codec's spec too.
- From these, `isModel S m` for the model value the driver passes, and the codec's
  correctness (`codecOk`: each encoding decodes back; the generated codecs come with their specs).

It is cheap (pure functions, a few dozen lines of Go) and it runs the whole toolchain end to end —
translation, a spec, a proof, a link — before any hard spec exists.

## Variants

The goal is one statement about one deployment. Variants of it (below) are for your own tests, to
reach paths the given workload reaches rarely, never a replacement of the goal:

- **failures** the model lacks: a crash and restart of a node, or, over an in-process network without
  faults, a partition (a node cut from the others and mended) and a slow node;
- **reconfiguration**: adding or removing a member under load;
- **persistence**: stop and restart the whole cluster, then check that acknowledged writes survive
  (a "restart" example: the check is a read after restart);
- **the target's harder features**: transactions, watches/subscriptions, leases, compaction;
- **two clients of different kinds**: a reader and a writer path that the target serves differently.

The same recorder and model, a different driver.

## Running the examples as tests

- Run the deployment as Go: the kit's own test (its `_test.go`, or the challenge's `CLAUDE.md`) runs
  every machine, as processes or in one process over loopback. Then under `go test` with a larger
  workload, **many times** (`-count=100`), with the race detector, randomized delays in the transport,
  and short timeouts. A panic is a bug in the target (the given driver, the driver's model and remote library
  are proved); record it per `TRUST.md`.
- Your tests go in the kit's Go module beside the given ones, in files of their own; none of them is
  translated (keep them out of the Goose project's packages, or in `_test.go` files).

## Direct checks (required, in the stress test only)

The executable test's porcupine check sees only the few operations it records, so a protocol bug shows
in it rarely. Alongside it, check the protocol's invariants directly in the stress test: each client
request takes effect at most once (make every command unique, a read included, and record the replicas'
executions); the replicas' executed sequences are prefixes of one another; every reply carries the
identity of the request it answers; for a consensus protocol, one leader per term, no two different
commands applied at one index, no server losing an entry it applied. These catch duplicate executions
and divergence at once, and a test that fails is how a bug becomes a finding.

Keep them out of the theorem: they belong in your stress test, never in the deployment. The proof
covers every schedule
anyway, so it establishes what these invariants say wherever the history depends on them, in the form
the proof finds convenient; a check in the deployment would make the theorem also state the invariant in the
check's own concrete form (its data structures, its hooks), at a cost and with no gain in coverage.
And a check must never be stronger than what the protocol guarantees (a check of a property the
protocol does not promise turns a correct schedule into a "bug"): state each one as the protocol's
own paper or documentation does, and when a check fires, first ask whether the check is right.

Show once that the history check can fail: plant a bug that breaks consistency (a read that returns a
stale reply, an overwrite that ignores versions) in a scratch copy and see the driver panic. A check that
cannot fail makes the theorem say nothing; a model whose Go `Step` accepts everything is such a
check, and a finding about the challenge.

## Spec-guided testing (optional)

Not a phase: in earlier runs it found nothing the provers did not, at 15-30 minutes a stage. Use it,
timeboxed, when a stage adds a pure model of the protocol that proofs will not exercise soon (the
model is large, and its first proof is far off); otherwise skip it. When used, test the specs against
the Go code before proving:

- **Canonical form** of a spec: `own σ ∗ ⌜Pre σ args⌝ -∗ WP f args {r, ∃ σ', own σ' ∗ ⌜Post σ args r
  σ'⌝ ∗ …}` with `Pre`, `Post` decidable functions of the pure records the predicates are indexed by
  (`PRINCIPLES.md`, "Records").
- **A test-only abstraction function** per record type (Go state → record), trusted for testing,
  checked later by the proof of the representation predicate.
- **Instrumentation** records `(σ, args, r, σ')` at each call as JSON; a Lean executable evaluates the
  Lean `Pre`/`Post` on the traces (the spec itself, not a Go transcription of it).
- **Readings**: `Post` violated → the spec is false. `Pre` violated on a normal workload's trace → the
  spec is stronger than its callers allow. `Pre` never satisfied → it is vacuous.
- **Lock invariants** asserted at each `Unlock`; trust-boundary libraries (storage, RPC, logging)
  exercised with random call sequences against their specs' pure models.

Testing does not check a spec's resources (ownership, fractions, invariants, atomicity): only proofs
do. Do not test the trace checker itself (tamper and mutation self-tests): it is test tooling.
