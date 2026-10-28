# What makes a good spec

The judgments the code and the proofs cannot make for you: most choose between specs that are all
true. Each comes from a review, the user's or the compactor pilot's (`notes/spec-first-study/`);
`examples/` shows them applied.

## Requirements

A spec failing one of these is wrong, whatever else it does well.

- **True of the code.** Check it against the Go source at the pin; a trust-boundary axiom against the
  library's code or documented behavior. A WP excludes panics: a precondition under which the code
  can panic is false.
- **Sufficient for every caller.** Each caller can establish the precondition, and the postcondition
  gives what its proof needs: every caller, not the one in mind (a server method has internal users
  and a gRPC handler). When the vocabulary changes, judge against the callers as restated.
- **Faithful to concurrency.** Concurrent callers need persistent contracts; once-only or exclusive
  use needs a token.
- **No unneeded premise.** Each premise is one the code needs or one a stronger result needs, or a
  scope restriction marked as such and filed (`issues/`, or a decision). Compare a configuration
  premise with what the Go code accepts (`time.ParseDuration` takes negative durations).

## Strength

- **Prefer the stronger spec, comparing whole specs.** A spec is at least as strong as another if the
  other can be proved as a layer on top of it. `{{ AU }}` is as strong as `{{ ⌜Q = True⌝ ∨ AU }}`,
  though its precondition is stronger: a caller with the state in an invariant builds the trivial AU.
  Do not judge a pre or a post in isolation.
- **No spec that is the disjunction of alternative specs.** Keep the stronger; the other is a layer.
  A case split on the input (a read-only vs a writing transaction) is not such a disjunction.
- **No vacuous guarantee.** For each disjunction, ask whether its weak side is ever false
  (`appliedErr ∨ srvMaybeDeposited`, the latter provable from nothing). A parameter that appears only
  in a precondition, chosen by the caller per call, constrains nothing. For a family of axiomatized
  predicates, try `True` (or the predicate itself) as a model: if every axiom still holds, the family
  says nothing.
- **A postcondition says what the caller inspects.** Not `fun _ => R` when the caller tests `err` or
  destructures the result.
- **Facts that can be combined.** A fact at an unknown point (a clock reading `T`) unrelated to what
  the caller already holds can never be chained with another.

## Abstraction

- **The spec of an API, not of an implementation.** Another reasonable implementation of the same
  API has the same spec (etcd's `Put`: a single in-memory server, no raft). No ghost names, internal
  records or fields, internal namespaces in masks, or the implementation's certificates and logs.
- **The vocabulary is part of the spec.** Improving a spec includes replacing or redefining the
  predicates it is written in, not only how it combines them.
- **A client does not unfold the spec's definitions**, nor another package's (its contracts,
  predicates, the initializer's facts by position). Each unfold is a missing law of the owning
  package. Find them all, mechanically (every `unfold`, `iunfold`, `simp only [...]`, positional
  `icases` in the callers), not from memory. A proof-only definition (a loop invariant) goes in a
  module only that proof imports.
- **Every premise has a source the client sees**: a spec or a law of the API, not the
  implementation's internal lemmas (`Start`'s `kvBuilt` needs `NewServer`'s post and an allocation
  law).
- **No constant or conjunct whose reason you do not know.** `+ 4`, `2 ^ 62` are proof slack; a fact
  of every reachable state is a law of the vocabulary, not one operation's post. Do not copy a
  conjunct from a sibling spec without knowing why it is there.

## Shape

- **TaDa, not HoCAP.** No caller-provided predicate as a parameter of a library predicate
  (`isStaticCluster … snapOk`). The library's specs take and give back client-owned ghost state (the
  set of snapshots made: making one takes the set and gives it back with the new snapshot; receiving
  one gives a witness that it is in the set), and the client keeps whatever invariant it wants over
  it (etcd: every snapshot's data is empty; an app that makes none: the set stays empty).
- **Linearizability is the caller's atomic update, written in the triple**: not behind a helper
  definition (`kvOpAu1`), and in the shape of the closest sibling spec (the server's `Put` and the
  client's `kv.Put`).
- **The caller's `Q` carries what the caller needs.** No witness or history predicate beside it
  (`kvWas γ σ`). A stale read still fires the update at the current state, and answers from a past
  state of it.
- **One general spec; special cases are instances.** No predicate or spec family for a special case
  beside the general one (`isStaticCluster` beside `isDynamicCluster`): it splits the proof in two.
  No reconfiguration is a run of the proof with reconfiguration; auth disabled is a state. A mode
  variant (`spec`/`specOn`) is at most a development hack to put off merge conflicts, never the
  finished spec.
- **After a change, drop what existed only for what it changed** (the `⌜Q = True⌝ ∨` of reads that
  once took no atomic update).

## Resources

- **An exclusive resource the code needs is covered by a token every caller can supply.** A contract
  `{{ True }}` over an implementation that needs a reader slot cannot be met. `threadTok` is one such
  token (a reader slot of sorts: it bounds the live goroutines); another is fine if all callers have
  it. Do not make callers thread a resource only the proof's bookkeeping needs.
- **A once-only resource is not spent per call.** Check retry and loop paths (a failed call retried
  with the same argument spends it again); make the exception depend on the value (a persistent
  one-shot fact), not on the call.
- **Read the definitions of the resources a spec takes**, not only their names: a predicate chosen
  for the access it gives may also assert what the function breaks (a store reader asserting "never
  compacted" in a compaction's spec).
