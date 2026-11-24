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
- **No Hoare triples or other Iris function specs, not even hidden.** A function's contract at the
  trust boundary is an axiom in that function's file (`Proof/<pkg>/<fn>.lean`), like every other
  trust-boundary spec. Hidden forms count too: a premise bundle whose definition unfolds to a triple
  or WP (`putget_safe`'s `Hprem : ⊢ etcdstart.premises …`, holding `bootstrapContract`, a triple for
  `etcdserver.bootstrap`, with `bootMarshal`, `rnLoggerZapOk`, `rnTimeoutDetectorOk`); an Iris
  entailment about a package's values (`Hctx : ContextReadErrs`); a type class carrying a function's
  body or contract (`[DialWithBalancerBody]`).
- **What may remain a premise:** genuine start-state and environment facts (files as on disk,
  unused addresses, `ETCD_VERIFY` off), each with a compiled satisfiability witness (the premise
  gate refuses a statement without one), and the package-assumption classes of the translations
  (`<pkg>.Assumptions`, field layouts) listed as trusted.
- **The thread and step bounds.** `Robust crashing stable g threads bound` takes them separately.
  `bound` (steps) is as high as the proof allows (`2^63 - 1` through `goose_dist_adequacy_below`,
  or the proof's own cap, e.g. raft's `readyFits` at `2^61`), and the header says what caps it.
  Never lower `bound` to get a thread cap. `threads` is a cap only when the proof needs one, a named
  constant from the real limit (net/http's `2^30` reader slots); otherwise `threads := bound + 1`
  (no execution under `bound` steps reaches it, so it excludes nothing), still named. No bare
  literals anywhere in the statement: name constants or use abstract facts (`maxAddr`).
- **Fix the extensions** (an instance list such as `kvnetExts`), and state their environment
  assumptions (closed world, one process per file system, ...) in the header's prose.
- **Reuse audited definitions.** Prefer premises and vocabulary already reviewed over new ones.
- **Check the statement is not vacuous.** Besides the Go non-vacuity tests, every premise bundle
  must be satisfiable in Lean (a past statement held because a premise implied `False`).
- **The header is the plan, concisely.** What it says, the premises and why each remains, the
  extensions and their environment assumptions, what is trusted. Technical, present tense: no
  history ("adapted here", "added on ..."), no narrative; those go in `notes/`. The same for every
  trusted file's documentation.
- **Example:** `examples/kvnet.md` (a decent statement, with what to improve).

## Checklist before the statement packet

1. **Unfold every premise and every class** in the statement down to its kind, and classify it:
   - *start state* (files on disk, empty roots, fresh process) — allowed, with a witness;
   - *environment* (address unused, nothing else touches the tree) — allowed, with a witness, or prose
     for an extension's assumption;
   - *package assumption* of a translation (`<pkg>.Assumptions`, `FieldAssumptions`, a name's model) —
     allowed, listed as trusted;
   - *a pure fact the program could check* (configuration validity, lengths, address syntax) — not
     allowed: move it into Go (validate, `return`), with a Go non-vacuity test;
   - *a function contract* (a triple, a WP, a class carrying a body or contract) — not allowed: an
     axiom in `Proof/<pkg>/<fn>.lean`;
   - *an Iris assumption* (any `⊢ …`, any entailment over ghost or package state) — not allowed.
2. **Bounds:** `bound` the highest the proof allows, never lowered to cap threads; `threads` a cap
   only if the proof needs one (from the real limit), else `bound + 1`; both named, each with why.
3. **No bare literals:** every size, count and bound a named constant or abstract fact.
4. **Non-vacuity:** the Go test (validation passes, every assertion reached, many seeds) and the Lean
   satisfiability witness of the premises; plus a concrete example instance.
5. **Extensions** fixed and listed; their environment assumptions in prose.
6. **Trust** listed in the header: translations, models, package assumptions, extensions, axioms.
7. **Header** concise and technical, no history.

## Process

1. Survey the API's real uses; write the driver's section list (behavior → call sites relying on it).
2. Write the driver and its deployment (`cmd/*`, the robust harness `examples/lib/robust`); run it
   for real (network namespaces, `netem` where the extension allows faults) and write the
   non-vacuity tests.
3. State the theorem (layout above); build the statement and an empty proof skeleton.
4. Run the checklist, then send the statement packet for review (Upamanyu reviews top-level
   statements asynchronously: keep going): the statement, the driver's section list, every premise
   with its kind and why it remains, what is trusted (extensions, models, axioms it rests on).
5. Prove it: specs, then invariants, then independent proofs (CLAUDE.md, "Proof writing"); track the
   remaining axioms with an `etc/tcb-collections/<example>.txt` collection, driven to empty.
