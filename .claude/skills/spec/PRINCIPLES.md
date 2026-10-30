# What makes a good spec

The judgments the code and the proofs cannot make for you; most choose between specs that are all
true. Each rule says why, and points to where it was learned: an example in `examples/` (the spec,
the critique, the result) or a review of the compactor pilot in `notes/spec-first-study/`. Open those
only for the rules your target touches.

Two kinds: the **hard rules** (their section below) must all hold, and a spec breaking one is wrong
however good it is otherwise. Everything after them is a **preference**: weigh them against each
other to choose among specs that keep the hard rules, and say so when you knowingly depart from one.

## Scope

These judgments are for specs that cross a package boundary: what another package's proof sees. An
internal helper's spec, used only inside its own package, may simply mirror its code.
(`notes/spec-first-plan.md`, Review)

## Hard rules

A spec that breaks one of these is wrong, whatever else it does well, and is not done.

- **Sound: true of the code**, including no panic under its precondition (a WP excludes panics); a
  trust-boundary axiom true of the library's code or documented behavior.
- **Complete: sufficient for every caller**: each caller can establish the precondition and gets from
  the postcondition what its proof needs. All callers, not the one in mind; when the vocabulary
  changes, the callers as restated. A contract an implementation must meet (an environment's
  interface, a callback) is complete only against the implementation's Go body when its own spec is
  unproved: every value the body reads from an argument (a context's `Value(key)`, a field) needs a
  premise. (The compactor's `compactableOk` passed five reviews checked against
  `EtcdServer.Compact.spec`, a `sorry`, and failed at the first glue: `Compact` reads
  `ctx.Value(TraceKey{})`; M2, `notes/m2-plan.md`, 2026-10-28.)
- **Local**: a spec is about its function's footprint, the state that function touches, and nothing
  else, so that a change elsewhere (a new feature, a conjunct added to some other component's
  predicate) leaves the spec and every proof that uses it untouched. Take the footprint, not an
  aggregate that contains it (a whole server row, a boot bundle every stage adds to); a caller
  holding the aggregate splits it, `core ∗ rest`. (The snapshot work, 2026-10-19 to 10-27: a spec
  over the server's whole apply row broke when auth added a conjunct to the row; one index had to be
  "kept by every frame", about 50 files; the boot contract accreted a clause per stage.)
- **Faithful to concurrency**: concurrent callers need a persistent contract; a once-only or
  exclusive use needs a token.
- **No unneeded premise**: each is one the code needs, one a stronger result needs, or a scope
  restriction marked as such and filed (`issues/` or a decision). A configuration premise is no
  stricter than what the Go code accepts. (`pilot-review-1.md`)
- **One spec per function; special cases are instances**: one proved spec per function, general
  enough for every case. No predicate or spec family for a special case beside the general one (a
  static cluster beside a reconfigurable one), which splits every proof above it in two; no
  reconfiguration is a run of the general proof. The same holds of modes (auth on and off, compaction
  on and off): a mode is part of the state (`E.authMode`, `ρ.kv.cmp`), not a second spec. A variant
  statement a client finds handier is fine only as a corollary of the one proof (`<fn>.spec_R :
  <fn>.spec → <fn>.specR`, `storage/mvcc/ReaderSpecs.lean`), never a second proof. A step that would
  start a family goes to the user first (`notes/spec-first-plan.md`, "Who decides"). (Auth's on/off
  specs, 2026-10-25 to 10-28: about 3.5k lines of copied proofs, every other track's change made
  twice, `notes/auth-mode-merge-plan.md`; M2's round-1 repair `8950d80bf2`, reversed by the user,
  `notes/m2-plan.md` on `m2`.)

## Preferences: strength

- **Prefer the stronger spec, comparing whole specs.** One spec is at least as strong as another if
  the other can be proved as a layer on top of it; so a stronger precondition can still make an
  equally strong spec, and a pre or a post is never judged alone. (`range.md`, critique 2)
- **No disjunction of alternative specs** (a precondition "trivial result, or the caller's atomic
  update"): keep the stronger, the other is a layer. A case split on the input is not one.
  (`range.md`, critique 2)
- **No vacuous guarantee.** For each disjunction, ask whether its weak side is ever false: one that
  always holds makes the statement say nothing (`put.md`, critique 1). A parameter that appears only
  in a precondition, chosen by the caller per call, constrains nothing (`pilot-review-3.md`). If every
  axiom of an axiomatized family still holds when its predicates are read as `True`, the family says
  nothing (`pilot-review-1.md`).
- **The postcondition says what the caller inspects**: not a constant when the caller tests the error
  or destructures the result. (`pilot-review-1.md`)
- **Facts that can be combined**: a fact at an unknown point (a clock reading) that is not related to
  what the caller already holds can never be chained with another. (`pilot-review-1.md`)
- **Know the margin**: where the postcondition is weaker than what the code guarantees, say what the
  code guarantees. (`notes/spec-first-plan.md`, Review)
- **One spec, a gated row, not two specs**: a stronger variant that holds only under a condition the
  caller knows (the auth mode) is a row `□ (⌜cond⌝ → …)` of the one spec, not a second spec; when
  the condition is there only because a trust-boundary axiom is too weak to give the row
  unconditionally, the docstring names that axiom as the margin. (`authinfo.md`)

## Preferences: abstraction

- **The spec of an API, not of an implementation**: another reasonable implementation of the same API
  would satisfy it unchanged (for a replicated server: a single in-memory server). No ghost names,
  fractions, helper definitions that hide part of the statement, internal records or fields,
  internal namespaces in masks, or the implementation's own logs and certificates. (`put.md`,
  critique 2; `notes/spec-first-plan.md`, Review)
- **The vocabulary is part of the spec**: improving a spec includes replacing the predicates it is
  written in, not only rearranging them. (`put.md`, critique 2)
- **A client does not unfold the spec's definitions, or any other package's**: each unfold is a
  missing law of the owning package. Find them mechanically (every `unfold`, `iunfold`, `simp only
  [...]` and positional destructuring in the callers), not from memory. A proof-only definition goes
  in a module only that proof imports. (`pilot-review-5.md`)
- **Every premise has a source the client sees**: a spec or a law of the API, never the
  implementation's internal lemmas.
- **No constant or conjunct whose reason you do not know.** A numeric bound in a post is usually the
  proof's slack; a fact that holds of every reachable state is one law of the vocabulary, not a
  conjunct of each operation's post. Do not copy a conjunct from a sibling spec without knowing why it
  is there. (`put.md`, critique 5)

## Preferences: shape

- **TaDa, not HoCAP**: no caller-provided predicate as a parameter of a library's predicate (a
  cluster predicate taking "what a snapshot's data means"); such a parameter changes every use of the
  predicate when it changes. Instead the library's specs take and give back ghost state the client
  owns (the set of snapshots made: making one takes the set and returns it with the new snapshot;
  receiving one gives a witness that it is in the set), and the client keeps whatever invariant it
  wants over it (one client: every snapshot's data is empty; a client that makes none: the set stays
  empty).
- **Linearizability is the caller's atomic update, written in the triple**, not behind a helper
  definition, and in the shape of the closest sibling spec (a server operation and the client
  operation that calls it). (`put.md`, critique 4)
- **The caller's result predicate carries what the caller needs**: no witness or history predicate
  beside it. A read that may be stale still fires the update at the current state, and answers from a
  past state of it. (`range.md`, critique 1)
- **One general spec; special cases are instances**: a hard rule ("One spec per function", above).
- **After a change, drop what existed only for what it changed.** (`range.md`, critique 2)

## Preferences: resources

- **An exclusive resource the code needs is covered by a token every caller can supply**: a contract
  with no resource over an implementation that needs one (a reader slot) cannot be met
  (`pilot-review-1.md`). A thread token is one such token (it bounds the live goroutines, as reader
  slots must be bounded); another is fine if all callers have it. Do not make callers thread a
  resource only the proof's bookkeeping needs. (`put.md`, critique 3)
- **A once-only resource is not spent per call**: check retry and loop paths; make the exception
  depend on the value (a persistent one-shot fact), not on the call. (`pilot-review-2.md`)
- **Read the definitions of the resources a spec takes**, not only their names: a predicate chosen
  for the access it gives may also assert what the function breaks. (`pilot-review-2.md`)
- **When only some clients need a resource the library hands back to be duplicable, let the client
  choose its persistence where it gives it** (a persistent update in, a persistent credit out:
  `propCredit γ P := if γ.dup then □ P else P`, `dup` chosen at allocation), instead of adding
  identification state (a registry) that every client threads. (raft's `node.Propose`, 2026-10-29,
  `notes/spec-first-study/raft-propose-dup-spec.md`)
- **Know what it rests on**: the axioms a spec depends on (`etc/tcb-report.py --roots`), whether a
  tester covers them, and how much of the pre and post is pure and decidable. The tester is the Test step
  of `notes/spec-first-plan.md`: instrumented Go runs record each call's state, arguments and result,
  and the spec's decidable pre and post are evaluated on them, so the decidable part of a spec is
  the part checked before any proof.

## Preferences: measures

Preferences too, but counted for each spec: on its unfolded statement (as `etc/gen-interface.py`
renders it), or in its callers' proofs. Each is a cost; lower is better among specs that keep the
hard rules. (`notes/spec-first-plan.md`,
Review)

- **Coupling**: the other packages' predicates and definitions the statement mentions. Each is a
  place where a change in that package forces this spec, and its callers' proofs, to change: in this
  repository's history the main cause of spec revisions.
- **Size**: the statement's length, its binders and its premises: a cost to every reader and to
  every caller's proof.
- **Law coverage**: the laws exported next to each predicate (persistence, timelessness, fractions,
  agreement, exclusivity) against the laws its callers use. A missing law shows up as a caller
  unfolding the predicate.
- **Caller burden**: the unfolds of the spec's definitions in its callers' proofs, and the *glue
  lines* per call. A glue proof is the proof of a caller whose body only passes state between its
  callees, proved from the callees' specs alone; its glue lines for one call are the lines it spends
  turning what it holds into the spec's precondition and reshaping the postcondition into what it
  needs next. A spec that fits its callers costs about one line, the `wp_apply`; dozens mean its
  shape is wrong for them (the server's `Put` once cost its gRPC handler about 60 lines of
  repackaging, `kvPutOk_of_server` in `api/v3rpc/ServerKV.lean`, 2026-10-27).
