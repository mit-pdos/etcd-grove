---
name: robustness
description: Formulate a top-level robustness theorem in this repository — write the driver program (the Go client that exercises a system's or library's client API and panics when a property fails), its deployment, and the `Robust` statement over it, ready to be proved. Use when asked to state a new top-level result, write a driver for a system or library (etcd, raft, gRPC, net/rpc, net/http, ...), or review or restate an existing `TopLevelRobustness` statement.
---

# Formulating robustness theorems

**Goal:** a top-level result that says something worth trusting about the real code, with as little
in its statement as possible. Every example's top-level result is an instance of `Robust`
(`Robustness/Statement.lean`; read `notes/robustness.md` and CLAUDE.md's `Robustness/` bullet):
in every execution of the deployment's programs (machines that may crash and restart, machines that
never crash, every fault the extensions allow), no thread is stuck and none has an unrecovered
panic. A property is therefore stated **in Go**, by a program that panics when it fails, never as a
Lean predicate over traces. The driver *is* the specification.

## The driver

The driver is the Go program (usually a client, sometimes also the server side) whose panics state
what we rely on. Write it as a spec, not as a test:

- **Exercise the client API, broadly.** Call every operation of the API that its real users rely
  on (survey how etcd, k8s and the dsverify kits use it, and say so in the plan), with arguments,
  orders and concurrency chosen nondeterministically.
- **As nondeterministic as possible.** Random choices (`rand`), concurrent goroutines, arbitrary
  interleavings, arbitrary inputs within what the API accepts. Every choice the driver leaves open
  widens the set of executions the theorem covers. The theorem is proved for **all** of them, so
  breadth costs nothing at run time and is the whole point.
- **Do not steer toward interesting executions.** No weighting, retry loops, sleeps or
  orchestration whose only purpose is to make a rare case likely in testing. The proof covers every
  execution the program can have *in principle*; a driver complicated to reach corner cases in
  practice is harder to read and proves nothing more. Prefer the simplest program whose set of
  possible executions contains the corner cases.
- **Easy to read.** One clearly named section per behavior relied on, each with a one-line comment
  stating the property, exercising it, and panicking (`panic(...)`) if it fails. A reader should be
  able to review the driver as the spec of the system or library.
- **Assert only what is guaranteed.** Faults (crashes, cut connections, delays, refused dials, lost
  or duplicated datagrams) come from the environment, so assert properties that hold under every
  fault the client cannot rule out: check the results of operations that reported success; handle
  errors without panicking (unless the API guarantees no error). Checkers for linearizability etc.
  (porcupine) run inside the driver and panic on `false`.
- **Report by panicking, never by exiting.** `os.Exit`, `log.Fatal` and loggers' `Fatal` are safe
  runs under `Robust` (Perennial models exit as `AngelicExit`); `etc/exit-check.py` refuses them in
  a driver.
- **Faults come from the environment, never from the program.** Don't inject duplicates, drops or
  reorderings in the driver or the system's own transport; choose an environment (a net or UDP
  extension, crashing machines) whose semantics allows them.

## The deployment and the statement

- **Layout** (CLAUDE.md): `Spec/<example>/TopLevelRobustness.lean` states it (`def <name>.spec :
  Prop`, nothing else: the file to audit); `Proof/<example>/TopLevelDefs.lean` holds the programs
  and definitions it names (a defs module); `Proof/<example>/TopLevelRobustness.lean` proves it.
  Strongest theorem, plainest name.
- **No pure premises the program can establish.** Configurations (member lists, addresses, options,
  sizes) are generated or read by the Go program and validated in Go (`if !ok { return }` is a safe
  run); the theorem then covers whatever the code produces. A validation that might never pass gets
  a **Go non-vacuity test** showing it passes and the real path (each assertion) is reached, over
  many seeds.
- **No function-contract premises.** A contract of a function at the trust boundary is an axiom in
  that function's file (`Proof/<pkg>/<fn>.lean`), never an Iris premise of the top-level statement.
- **What may remain a premise:** genuine start-state and environment facts (files as on disk,
  unused addresses, `ETCD_VERIFY` off), each with a compiled satisfiability witness (the premise
  gate refuses a statement without one). Name bounds by constants or abstract facts, never literals.
- **Reuse audited definitions.** Prefer premises and vocabulary already reviewed over new ones.
- **Check the statement is not vacuous.** Besides the Go non-vacuity tests, every premise bundle
  must be satisfiable in Lean (a past statement held because a premise implied `False`).

## Process

1. Survey the API's real uses; write the driver's section list (behavior → call sites relying on it).
2. Write the driver and its deployment (`cmd/*`, the robust harness `examples/lib/robust`); run it
   for real (network namespaces, `netem` where the extension allows faults) and write the
   non-vacuity tests.
3. State the theorem (layout above); build the statement and an empty proof skeleton.
4. Send the statement packet for review (Upamanyu reviews top-level statements asynchronously: keep
   going): the statement, the driver's section list, every premise with why it remains, what is
   trusted (extensions, models, axioms it rests on).
5. Prove it: specs, then invariants, then independent proofs (CLAUDE.md, "Proof writing"); track the
   remaining axioms with an `etc/tcb-collections/<example>.txt` collection, driven to empty.
