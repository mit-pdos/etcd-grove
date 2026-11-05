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

**A smaller API is not a narrower scope.** A redesigned API keeps a spec for every function that
already has a proved spec (a linked result: the package's `Link.lean`), and for every feature those
specs cover (watch filters), whether or not today's clients call it. Minimizing the vocabulary is a
choice among specs of the same functions; dropping a verified function to save a predicate makes
verified code unverified. Functions with no proof today may be left out, marked as such. (The mvcc
API's round 10, 2026-11-02: it left out `NewStore`, `Restore`, the store's views and watch filters,
all verified; the user: "Do not leave out any methods that we have verified previously.")

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
- **An unsound candidate is replaced by a sound one, not dropped**: every function in the scope
  keeps a spec. When a candidate turns out false (it lets a client reach a path that breaks
  another spec's guarantee), find what is true of the function: often a precondition that names
  the case the code handles (a mode of the object, a token only the safe path produces), not the
  removal of the function from the API, which leaves its callers with nothing. (The mvcc candidate
  API, round 2, 2026-11-01: `store.Write`'s candidate let a watched store commit without notifying
  its watchers, and was removed; the user: "If one possible spec was unsound, that just means we
  need a better spec.")
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
  The exception is the trust boundary: a fact only an axiom gives does not go into a proved spec,
  which would put the axiom under every result using that spec. It is a separate trust-boundary spec,
  the proved one's post plus the assumed fact, and only the callers that need it take it. Before you
  strengthen a spec in place, check whether its proof is a theorem (`etc/tcb-report.py --check`
  shows which collections gain an axiom). (`context.WithTimeoutBackgroundMd`, 2026-10-29: folding
  it into the proved `WithTimeoutBackground` would have put an axiom under ten collections for
  authkv's one fact; the user kept the split.)
  The split needs a second spec of the same function. When the proved spec itself must carry the
  fact (its proof is the only place it can come from), there is nothing to split: strengthen the
  axioms in place, list for each the collections that now rest on the stronger claim (`--check` does
  not flag a same-name change), and put it to the user. Before strengthening, check what the axiom
  admits beyond the code's own uses: a stronger claim can be false on an input the old one covered
  harmlessly. A post that says a call returns claims it returns on every input the premise admits:
  check Go's stack and memory there too (a recursion per level of a deep message). (`irr-depth.md`) (`watcher.Watch` with auth on, G2, 2026-10-30: `examples/watch-auth.md`.)

## Preferences: strength

- **Prefer the stronger spec, comparing whole specs.** One spec is at least as strong as another if
  the other can be proved as a layer on top of it; so a stronger precondition can still make an
  equally strong spec, and a pre or a post is never judged alone. (`range.md`, critique 2)
- **No disjunction of alternative specs** (a precondition "trivial result, or the caller's atomic
  update"): keep the stronger, the other is a layer. A case split on the input is not one.
  (`range.md`, critique 2)
- **Two incomparable specs often have a common generalization: look for it before choosing.** When
  two candidates differ in which share of a resource they take (an owned half that can still change,
  a frozen persistent fraction), one spec over the share, given back unchanged, has both as
  instances and is stronger than each. Put the options to the user as statements side by side,
  checked, with which is stronger by the layering test. (mvcc's `Restore` and the new backend's
  post-lock hook, `plHookAt B'.γB dq f`, 2026-11-03: the user chose it over the owned-`nil` loan and
  a frozen-hook contract.)
- **No disjunction a proof must handle twice**: a condition a guarantee holds under is one
  condition, not "this case or that case" each of which the implementation's proof, or a client's,
  would establish by a near-copy of the other's argument. Find the single condition the code's
  behavior turns on (the mvcc watch guarantee under compaction: "every revision from the watcher's
  first up to the compaction revision changes each key at most once", which is vacuous below the
  compaction revision, in place of "the compaction revision is below the watcher's first, or no
  revision changes a key twice"). An assumption is acceptable when it does not split the proof.
  (The mvcc API, round 11, the user, 2026-11-03.)
- **No vacuous guarantee.** For each disjunction, ask whether its weak side is ever false: one that
  always holds makes the statement say nothing (`put.md`, critique 1). A parameter that appears only
  in a precondition, chosen by the caller per call, constrains nothing (`pilot-review-3.md`). If every
  axiom of an axiomatized family still holds when its predicates are read as `True`, the family says
  nothing (`pilot-review-1.md`).
- **The postcondition says what the caller inspects**: not a constant when the caller tests the error
  or destructures the result. (`pilot-review-1.md`)
- **Do not overspecialize a spec to its users.** State what is true and generally useful of the
  function and its object, not the shape one client happens to consume today; a client's need is a
  test of completeness, not the spec's design. (The user, 2026-11-03.)
- **Keep a tool's temporary limitation as local as possible.** An assumption that exists only
  because a dependency's spec is too weak today (Perennial's sort needs at most `2 ^ 62` elements:
  a size bound no Go program needs, to be removed by improving Perennial) goes where the limited
  spec is used, so that removing it later touches one place: not a law about the object's state that
  every client threads. Without such a reason, a general law may well be the better spec. (The mvcc
  API, round 15, 2026-11-03: the sort's size facts at the `Range` contracts, `stateOk`, not a size
  law on the store's state; the user: "we're going to ultimately get rid of the explicit size limit
  assumptions ... so I want those assumptions as local as possible".)
- **Facts that can be combined**: a fact at an unknown point (a clock reading) that is not related to
  what the caller already holds can never be chained with another. (`pilot-review-1.md`)
- **Know the margin**: where the postcondition is weaker than what the code guarantees, say what the
  code guarantees. (`notes/spec-first-plan.md`, Review)
- **A size argument from fresh copies checks every path for aliasing**: an encoding counts each
  reference, a heap counts each allocation; one fast path that reuses a buffer (etcd's keys-only
  ranges reuse the index's key slices) turns "Go runs out of memory first" into a reachable panic.
  (`reply-size.md`, critique 2)
- **One spec, a gated row, not two specs**: a stronger variant that holds only under a condition the
  caller knows (the auth mode) is a row `□ (⌜cond⌝ → …)` of the one spec, not a second spec; when
  the condition is there only because a trust-boundary axiom is too weak to give the row
  unconditionally, the docstring names that axiom as the margin. (`authinfo.md`)
- **A new mode redefines the shared predicates in place, not mode-indexed copies**: when a mode widens
  what a family of predicates admits (compaction entries in the KV invariant), redefine the few that
  change, keep the text of the specs and predicates that carry them (read under the redefinition), and
  prove that the old mode means the old statements (laws, not `rfl`). Copies indexed by the mode must
  cover every carrier, and each review round finds one more that was missed. (`compaction-in-place.md`)
- **No arm the precondition excludes**: an error case of the code that the caller's premises rule out
  (`ErrFutureRev` under a certificate of the revision) is a sentence in the docstring, not a disjunct
  every caller must discharge; its proof branch is a contradiction. (`compaction-in-place.md`)

## Preferences: abstraction

- **The spec of an API, not of an implementation**: another reasonable implementation of the same API
  would satisfy it unchanged (for a replicated server: a single in-memory server). No ghost names,
  fractions, helper definitions that hide part of the statement, internal records or fields,
  internal namespaces in masks, or the implementation's own logs and certificates. (`put.md`,
  critique 2; `notes/spec-first-plan.md`, Review)
- **An API is stated over the abstractions it builds on, not over its dependencies' implementations**:
  where a package assumes a contract of a dependency (mvcc of its storage: `isKeyBackendG`), its
  API's statements take that contract, never the concrete dependency's predicates or configuration
  (`backend.newPostKP γB P …`, `bridgeParams P`); so the package works over any implementation
  meeting the contract, and the client that chooses the implementation discharges the contract for
  it (the server proves mvcc's storage contract for etcd's backend through the bridge, from the
  `bridgeParams d.P` it holds). A premise about the concrete dependency appearing in the API is the
  symptom. (The mvcc API's open law, the user, 2026-11-06: "mvcc should respect the abstractions it
  builds on.")
- **The vocabulary is part of the spec**: improving a spec includes replacing the predicates it is
  written in, not only rearranging them. (`put.md`, critique 2)
- **Canonical specs are per (concrete type, method); an interface value gets a bundle.** The
  canonicity that matters is a plain mapping from a concrete type and a method name (a promoted
  method included: Go puts it in the type's method set) to its one spec, in its spec file. A client
  holding an interface value whose dynamic type it does not track gets a separate predicate for it
  that bundles its interface's method triples, as Perennial's `sync.isLocker`
  (`Perennial/Proof/sync/Base.lean`), proved once from the concrete specs (as `Mutex_is_Locker`).
  Stating the API's specs on interface calls instead breaks the mapping; stating them on concrete
  methods and making clients unwrap fields (dispatch laws) costs glue in every client. One way to
  keep the text single: write each interface method's contract once at a receiver `(ty, v)` and make
  each concrete spec its instance. (The mvcc API, round 11, the user, 2026-11-03.)
- **A client does not unfold the spec's definitions, or any other package's**: each unfold is a
  missing law of the owning package. Find them mechanically (every `unfold`, `iunfold`, `simp only
  [...]` and positional destructuring in the callers), not from memory. A proof-only definition goes
  in a module only that proof imports. (`pilot-review-5.md`)
- **Every premise has a source the client sees**: a spec or a law of the API, never the
  implementation's internal lemmas.
- **A client's certificate is the cluster's**: a persistent fact a client takes from one call's
  reply into a later call (a revision reached) must hold at every member the later call may reach,
  so build it from what the members share (the cluster's raft log, the KV model), never from one
  member's ghost state (its store's certificate map); and check the tie it needs against the
  multi-member allocation, not only today's single-member producers. (`compact-client.md`)
- **A workload premise about a resource's later operations goes on the resource's only producer**,
  carried by the resource (as `apply.backendUnderQuota` on `storage.NewBackendQuota`, carried by the
  quota object; `grpcRepliesFit` on `grpc.start`, carried by the server tokens): the consumers'
  statements stay, and the premise is taken where a proof reaches the producer, not beside a sibling
  premise wherever that one sits. No law extracts the premise back from the resource; the docstrings
  of the results consuming it say they are conditional on it. (`reply-size.md`)
  The other way round: a premise on an operation must be provable by its callers from what they
  hold. A property of the whole earlier history (no revision so far writes a key twice) is not a
  later operation's premise (the compaction's): its callers cannot know it; it is the writers', or
  that of whoever already reasons about them (a watch client's workload, gated by the mode where
  only that mode needs it). (`watch-compaction.md`)
- **A contract between packages states the receiver's need, not the supplier's mechanism**: the
  server's `Txn` takes the depth of the request's model, not the gRPC handler's budget bound that
  implies it; the supplier proves the law from its mechanism to the need. The need is weaker to
  supply and names nothing of the supplier. (`irr-depth.md`, critique 2; the gRPC lease reads' contract keeps the
  server's header ids inside its answer and leaves the server's bounds premises to the theorem that
  discharges it, so the handlers' specs inherit neither (`lease-grpc.md`).
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
  The departure the user approved: a persistent predicate fixed when the object is created (a saved
  predicate, `crevPermIs`), which every value of a field satisfies, when the object's own locks
  already hold the shares a logically atomic spec would hand back and a client only reads the fact;
  it costs one premise on the writer and no client state. Say that it departs. (`c3-store-law.md`)
- **Linearizability is the caller's atomic update, written in the triple**, not behind a helper
  definition, and in the shape of the closest sibling spec (a server operation and the client
  operation that calls it). (`put.md`, critique 4)
- **A commit point the client chooses is an atomic update the library hands out.** When the client
  decides *when* a library step takes effect (raft's Ready: written to disk first, or at once), the
  library's spec gives the client an atomic update to fire at that moment, inside its own atomic step
  or whenever, and what the step permits (sending the batch's messages) is the update's post. The
  library does not name the client's mechanism: no "disk" predicate in raft, because a client may
  keep nothing durable. The state the update acts on is in the library's own terms (raft's state),
  and is exclusive only where soundness needs it. (raft's durable node API, 2026-10-31, the user's
  critique of candidate 4: `notes/STATUS.md`, "examples/kvdurable and the durable node API")
  The client-owned state is only the part the client's choice is about: for durability, raft's
  persistent fields (term, vote, log, snapshot), not the volatile ones, which stay in the library.
  Then a restart is no transition of that state, only a fresh library-side half built over it.
  (Same, the user's answer on candidate 5.)
- **No identification handles for the proof's bookkeeping** (`nodeInc`, incarnation tokens): key
  facts by values the client already has (the node object, the storage object). A handle only the
  proof needs is a resource every caller threads. (Same critique; see also "Do not make callers
  thread a resource only the proof's bookkeeping needs", `put.md`, critique 3.)
- **The caller's result predicate carries what the caller needs**: no witness or history predicate
  beside it. A read that may be stale still fires the update at the current state, and answers from a
  past state of it. (`range.md`, critique 1)
- **Pure premises go in the precondition**, as `⌜P⌝` conjuncts of the triple's `{{ … }}`, not as Lean
  implications before it (`P → {{ … }} e {{ … }}`): the two are equivalent, but the triple then reads
  as one contract, everything the caller must establish in one place. Proofs introduce them with
  `%H` in `wp_start`'s pattern; a caller discharges them in the `wp_apply` premise goal
  (`ipureintro`). Older specs still use implications; convert one when you change it. (porcupine's
  `Check*` specs, 2026-11-03, the user's request.)
- **One general spec; special cases are instances**: a hard rule ("One spec per function", above).
- **After a change, drop what existed only for what it changed.** (`range.md`, critique 2)

## Preferences: resources

- **An exclusive resource the code needs is covered by a token every caller can supply**: a contract
  with no resource over an implementation that needs one (a reader slot) cannot be met
  (`pilot-review-1.md`). A thread token is one such token (it bounds the live goroutines, as reader
  slots must be bounded); another is fine if all callers have it. Do not make callers thread a
  resource only the proof's bookkeeping needs. (`put.md`, critique 3)
- **A trusted statement never gives out a counted resource it did not take** (a `threadTok`, a
  receipt, a reader slot): such a resource is sound only because its total is fixed by the adequacy
  theorem (`threadToks threadBound ⊢ False`), and one an axiom produces has no such bound. In each
  post, name the caller that gave every counted resource. Give it back only once the real
  operation that used it is over, not when the call returns: a call can time out while the work it
  started goes on. Analogy with a modelled operation ("grpc forks a goroutine, and `wp_fork` gives
  a token") is no argument when the thing is outside the semantics: grpc's goroutines are not
  among the threads adequacy counts. (lease-ex's D1, 2026-11-02: the restated `grpc.serve` gave
  each run a `threadTok` out of nothing, and a blocking service could collect `threadBound` of them;
  the reviewer, checking against grpc-go, rated it true and left the accounting "uncertain". The
  first fix, the client lending its token to the run, failed the timeout case.)
- **A bound is reasoned about where it is owned, not in the specs between** (`notes/bounds-plan.md`,
  the user's, 2026-11-01): the adequacy theorem fixes the global constants (threads, steps, the
  workload); the owner of a bounded object (the invariant allocating the `RWMutex`, `WaitGroup` or
  counter) turns them into a protocol of unbounded use (a thread pool of reader slots, a wait group
  backed by thread tokens, a counter ticked by receipts); a client takes its `threadTok`, the owner's
  persistent handle, and named size bounds. So a new spec mentions no
  `threadBound`, `receiptBound`, `actualMaxReaders` or count of reader slots (`List.replicate 64 ...`);
  `etc/bounds-check.py --check` refuses new ones.
- **A size bound shared between specs is written with its named constant, not the number**
  (`opKeyMax`, `etcdKeyMax`, `leasingPfxMax`, ...; the user's, 2026-11-01): the name says why the
  bound is there, a change of the limit is one edit, and a caller composes named quantities. Define
  it next to the law that chose it, `@[word_unfold]` so that `word` sees through it. A literal is
  for a bound local to one function (a library's own overflow precondition, `< 2 ^ 63` for an
  `int64`). Not a predicate (`keyOk k`) for a single `≤`: `omega` and `word` do not see through one. Where a goroutine holds
  two read locks at once, the inner lock's slot is a counted stock at that call path only.
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

- **Abstractions**: the opaque predicates (and the resources) an API introduces, counted over the
  whole API, not per spec. The goal is that future proofs over the API succeed quickly: each
  abstraction is something every client proof must learn, thread and combine. Prefer one
  abstraction that subsumes several (the client-owned `mvccState` replaced the log's
  certificates, the revision tokens and the reader's floor), and a field of an existing state or a
  resource clients already hold (a thread token) over a new predicate. Judge each candidate
  abstraction by two questions: is the API strong enough for its reasonable users without it, and
  can an existing one carry it? (The user, 2026-11-02, on the mvcc candidate API's decisions.)
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
