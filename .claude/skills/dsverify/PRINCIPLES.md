# What makes a good spec

For every Hoare triple, predicate, law, invariant and hypothesis you write. Reviewers
judge by this file and by `examples/`. When the user critiques a spec, sharpen a principle here
(minimally); when the user approves one, add an example (its first version, each critique and what it
changed, the approved spec).

## Hard rules

- **Sound: true of the code**, including no panic under its precondition (a WP excludes panics). A
  premise the code needs that the target's API does not document is a finding (`TRUST.md`).
- **Complete: sufficient for every caller**: each caller can establish the precondition and gets from
  the postcondition what its proof needs. Glue proofs check this; write them.
- **Local**: about the function's footprint, the state it touches; frame the rest.
- **Faithful to concurrency**: callers that run concurrently need a persistent (duplicable) contract;
  a once-only or exclusive use needs a token; an exclusive requirement of the code is stated.
- **No unneeded premise**: each premise is one the code needs, one a stronger result needs, or a scope
  restriction with its reason. A premise that excludes a legitimate caller fails completeness.
- **One spec per function; special cases are instances.** No twin triples for modes (a security feature on/off, a
  feature on/off): one general triple whose mode is a parameter, the special cases one-line instances.
  Twins drift: every shared clause is edited N times and a missed copy breaks the derivations. One
  per function across the whole tree, too: a library function that already has a spec (in `Net/`,
  the main tree, Perennial) is used through it, never given a second one (`CHALLENGE.md`).
- **A hypothesis carries the real code's preconditions** (`TRUST.md`): a non-`nil` receiver, a token
  where the code is not thread-safe, a call made once where a second panics. Its precondition is
  never `True` for a function that can panic.

## Strength

- **Prefer the stronger spec, comparing whole specs** (pre weaker and post stronger), not clause by
  clause.
- **No disjunction of alternative specs** in a precondition; no vacuous disjunct in a postcondition
  (for each disjunction, ask whether its weak side is ever false).
- **The postcondition says what the caller inspects**: a returned error's meaning, not a constant.
- **Facts that can be combined**: a fact at an unknown point (a clock reading, a log length) related to
  something the caller can compare.
- **Know the margin**: where the post is weaker than what the code guarantees, say what the code
  guarantees and why the spec stops short; strengthen only when a caller needs it.
- **A gated row, not two specs**: a stronger variant under a condition the caller knows is a row
  `□ (⌜cond⌝ → …)` of the one spec.
- **A new mode redefines the shared predicates in place**, not mode-indexed copies: when a mode widens
  what a family of predicates admits, redefine the few that change, keep the text of the specs that
  carry them, and prove that the old mode means the old statements.
- **No arm the precondition excludes**: an error case the caller's premises rule out is not in the post.

## Abstraction

- **The spec of an API, not of an implementation**: another reasonable implementation would satisfy it.
- **The vocabulary is part of the spec**: improving a spec includes replacing the predicates it is
  written in.
- **A client does not unfold the spec's definitions, or any other module's.** Each unfold is a missing
  law; add it to the module that owns the definition.
- **Every premise has a source the client sees**: a spec or a law of the API.
- **A contract between packages states the receiver's need, not the supplier's mechanism.**
- **A workload premise about a resource's later operations goes on the resource's only producer**, not
  on every consumer.
- **No constant or conjunct whose reason you do not know.**

## Shape

- **TaDa, not HoCAP**: no caller-provided predicate as a parameter of a library's predicate. The
  library's specs take and give back ghost state the client owns (e.g. the set of items produced:
  producing takes the set and returns it with the new item; receiving gives a witness of membership);
  the client keeps whatever invariant it wants over it. A parameter predicate changes every use when it
  changes.
- **Linearizability is the caller's atomic update, written in the triple** (a logically atomic spec:
  the caller supplies an atomic update the library commits at its linearization point), not hidden
  behind a helper predicate.
- **A commit point the client chooses is an atomic update the library hands out.**
- **No identification handles for the proof's bookkeeping** (incarnation tokens, internal ids) in a
  public statement: key ghost state by what the client already has.
- **Pure premises go in the precondition**, as `⌜P⌝` conjuncts, not as Lean arguments before the
  triple (a client then cannot supply them from resources).
- **Records**: a predicate takes its object's state as one record of pure values holding only what the
  specs need (`PROOF-NOTES.md`).
- **A hub names each subsystem through its sealed slots, not its facts** (`HUBS.md`).
- **After a change, drop what existed only for what it changed.**

## Resources

- **An exclusive resource the code needs is covered by a token every caller can supply.**
- **A trusted statement never gives out a counted resource it did not take** (a thread token, a
  receipt, a budget unit). Reviews against the code miss this; the attack finds it (`TRUST.md`).
- **A bound is reasoned about where it is owned**: the adequacy theorem fixes global constants (threads,
  steps, workload size); the owner of a bounded object (the invariant allocating a lock's reader slots,
  a wait group, a counter) turns them into a protocol of unbounded use (a pool, tokens, receipts); specs
  in between take tokens and the owner's handle, never the numbers.
- **A field written only before publication is a persistent fact**, not a share. Under memory reuse,
  key such facts by an incarnation name the code already makes fresh (a new channel, an id); if it
  makes none, consider a code change (a fresh immutable header per incarnation, a fix recorded as
  such, `TRUST.md`, where the challenge allows code changes) before adding incarnation ghost names.
- **A field split among more than two holders is a smell**: simplify its ownership, or the code,
  before proving with it.
- **A once-only resource is not spent per call**: check retry and loop paths.
- **Read the definitions of the resources a spec takes**, not only their names.
- **Know what it rests on**: the axioms a spec depends on, and whether each is tested.

## Invariants

An invariant is a spec too: of what a shared object, protocol or subsystem keeps true for everyone.

- **Written in the interface, in full**: its body, its ownership (who allocates it, who opens it, which ghost
  state it holds and who holds the other halves) and the laws its clients use. A name with a `sorry`
  body is not a draft. This holds inside a package too, for the invariant of an object shared across
  threads: no interface review sees it, so its package writes it in full, with its lifecycle table
  (`LIFECYCLE.md`), before a proof relies on it.
- **The client keeps its own invariant** (TaDa, above): a library's invariant does not contain the
  client's facts.
- **Strong enough for its hardest step**: the step that must preserve it in the riskiest case
  (concurrent update, reconfiguration, restore, crash) is the first proof of its package in Prove,
  once the top functions are stated against `sorry`s (`SPEC-FIRST.md`); internal invariants included.
- **Admitting a new case into it is a Scope question**: list what the invariant rules out today and
  what becomes false once the case happens.
- **Sealed when a hub carries it**: `<sub>.runInv` behind a slot, with narrow elimination laws, so the
  body can change after a freeze without changing frozen statements (`HUBS.md`).
- **Owned bounds** (Resources, above) live in invariants; nothing else mentions the constants.

## Measures (reported with each review)

- **Coupling**: the other packages' predicates the statement mentions; each is a place a change
  elsewhere forces this spec to change.
- **Size**: the unfolded statement's length, binders, premises.
- **Law coverage**: the laws exported next to each predicate against those callers use.
- **Caller burden**: unfolds of the spec's definitions in callers' proofs; glue lines per call.
- **Scope premises**: premises restricting configuration or workload, each citing its reason.
