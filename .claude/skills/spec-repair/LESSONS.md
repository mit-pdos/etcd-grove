# Lessons from review

One entry per critique of a run: date, target, what the user said, the rule it became (in `SKILL.md`).

- 2026-10-27, `evals/` (the four cases: raft `node.Propose`, the B-tree's `ReplaceOrInsert`, the
  cache's `Get`, the client's `kv.Put`): thrown away, "too long to be useful for my feedback".
  Rule (`SKILL.md`, "Evals"): a case is one small target whose review fits one sitting.
- 2026-10-27, `EtcdServer.Put.spec` (iterating on candidates): "write the spec as we go in a temp
  file so I can see it in full" (candidate 2 had been an abbreviated sketch in chat). Rule
  (`SKILL.md`, "Iterating with the user"): the full candidate lives in a scratch file.
- 2026-10-27, `EtcdServer.Put.spec` (candidate 2, which bundled raft's log certificates into
  `srvLogLb`): "This spec should be the same spec that an alternate implementation would have ...
  an in-memory, single-server version of etcd that has no raft library and no srvLogLb." Rule
  (`SKILL.md`, review list): the alternative-implementation test for implementation detail.
- 2026-10-27, same: "When I ask for a spec to be improved, I'm generally wanting to change
  predicates that are used in that spec too." Rule (`SKILL.md`, "Repair"): the vocabulary is in
  scope.
- 2026-10-27, `EtcdServer.Put.spec` (candidate 3 kept a per-caller token `kvCaller s` for the
  server's RWMutex reader slots, "linear is the safe choice"): "Why is kvCaller needed? Would the
  spec be unprovable without it?" It was not needed: the caller's `threadTok` bounds the readers.
  Rule (`SKILL.md`, review list): question every bookkeeping resource a caller threads through.
- 2026-10-27, `EtcdServer.Put.spec` (candidate 4 took the AU as `kvOpAu1 γ (.put op) Q`): "get rid
  of kvOpAu1 as a helper definition, and just write the AU directly in the hoare triple. It should
  look like the client Put spec." Rule (`SKILL.md`, the wrapper item): AUs in the triple, and the
  closest sibling spec's shape.
- 2026-10-27, `EtcdServer.Put.spec` (candidate 5 copied `σ.rev + 4 < 2 ^ 63 ∧ kvLogOk σ ∧ …` from
  the client's `kv.Put`): "Why did you add the pure facts with random hard-coded numbers?" They were
  proof slack and facts of every reachable state. Rule (`SKILL.md`, review list): no unchecked copied
  conjunct or constant; reachable-state facts are a law of the vocabulary.
- 2026-10-27, `EtcdServer.Range.spec` (candidate 1 returned `kvWas γ σ ∗ □ Q σ`): "what's the
  point of kvWas? The Q predicate can maintain whatever facts are important". Rule (`SKILL.md`,
  review list): no witness predicate beside an AU's `Q`; a serializable read fires the AU too.
- 2026-10-27, `EtcdServer.Range.spec` (candidate 2 kept `⌜Q = fun _ => True⌝ ∨ AU …`, the path of
  serializable reads when they took no AU, after making every read take one): "What's the point of
  having Q = true in the precondition for the Range spec?" Rule (`SKILL.md`, "Repair"): after a
  change, drop what existed only for what it changed.
- 2026-10-27, same (the reason behind the last entry): "A spec that always requires the AU is a
  stronger spec, because the True ∨ AU spec can be proven as a layer on top by putting kvState in
  an invariant. In general, we should avoid specs that are really the disjunction of two alternate
  specifications, especially if one of those specs is strictly stronger than the others." Rule
  (`SKILL.md`, review list): no disjunction of alternative specs; keep the stronger.
- 2026-10-27, raft's `isStaticCluster` (the snapshot work gave it a parameter `snapOk : List LogEntry →
  List w8 → Prop` relating a snapshot's data to the committed log, so every use changed): "injecting
  predicates is like HoCAP style of specifications, but we want TaDa style specs". The snapshots made
  should be one client-owned ghost resource: making a snapshot takes it and gives it back with the new
  snapshot; receiving one out of raft gives a witness that it is in the set; etcd puts the resource in
  an invariant saying the data is empty, and an app that makes no snapshots keeps the set empty. Rule
  (`SKILL.md`, review list): no caller predicate as a library predicate's parameter.
- 2026-10-27, raft's `isStaticCluster` and `isDynamicCluster`: "having isStaticCluster separate from
  isDynamicCluster is another bad proof pattern, because it bifurcates the proof into stuff with
  reconfig and stuff without. In reality, no reconfiguration should be captured by the generic proof
  with reconfiguration." Rule (`SKILL.md`, review list): no special-case predicate or spec family
  beside the general one.
- 2026-10-27, `EtcdServer.Start.spec` (candidate: `{{ kvBuilt s γ ∗ threadTok }}`, with no candidate
  giving `kvBuilt`): "What's kvBuilt? How would the user of the EtcdServer specs gain kvBuilt?" Rule
  (`SKILL.md`, review list): every premise has a source the client sees.

## 2026-10-27, the compactor pilot's specs (first review, `notes/spec-first-study/pilot-review-1.md`)

The author's self-review by the rubric found 4 problems; the independent review found those and 5
more, the most serious a vacuous guarantee no proof would have flagged. Rules (now the reviewer's
"Failure patterns"): check an environment contract's resource against the implementing callee's spec;
check that the post carries what the caller inspects; for each disjunction ask whether the weak side
is ever false; try the trivial model of an axiom family; check that trust-boundary facts can be
chained with what the caller holds; check every mode variant; compare configuration premises with
what the Go parser accepts. And: give the review to a fresh reviewer, not the author (the author's
review missed the vacuous disjunct it had itself written).

## 2026-10-27, the compactor pilot's specs (second review, `notes/spec-first-study/pilot-review-2.md`)

Three blockers, two of them introduced by the first round's repairs (a once-per-run token spent by a
retried call; a reader resource asserting "never compacted" in `Compact`'s spec), and one false
positive (a Go issue reported as unrecorded that `issues/` already had). Rules (in the reviewer's
"Failure patterns"): check retry paths for once-only resources; read the definitions of the resources
a spec takes; in later rounds, look hardest at what changed. For the orchestrator: always run another
round after repairs.

## 2026-10-27, the compactor pilot's specs (rounds 3 and 4, `notes/spec-first-study/pilot-review-{3,4}.md`)

Round 3: a permit parameter quantified per call is vacuous (each caller picks it); a resource missing
since round 1 (the slice the run token should own) that two rounds had missed; a Go defect no spec can
fix (the compactor run before `Start`), resolved by a fork fix. Round 4: nothing in the first tier,
but its first-ranked finding had been fixed after its snapshot. Rules: a parameter only in a
precondition, chosen by the caller, is vacuous; name the commit under review and compare with `HEAD`
before reporting; give the reviewer a context bundle (rounds take about 9 minutes, mostly reading).


## 2026-10-27, the compactor pilot's phase 3 (the `Run` proofs)

Four review rounds never counted the unfolds a client makes of another package's definitions; the
two `Run` proofs had three (the clock's `clockOk`, mvcc's initializer fact taken by position,
Perennial's `isContextDef`), each a missing law. The user's rule: a client of a good spec does not
unfold its definitions. Rule (the reviewer's "Failure patterns", and phase 3 of
`notes/spec-first-plan.md`): list every cross-package unfold in the callers' proofs, add the law to
the owning package, and freeze only with the list empty.

## 2026-10-27, the compactor pilot's round 5 (before the freeze, `notes/spec-first-study/pilot-review-5.md`)

The author's list of cross-package unfolds (made by grepping for the definitions the author had in
mind) missed one (`fmt.argsOk` in `New`); the fresh reviewer found it by reading every caller's
`unfold`/`simp only [...]`. Rule: build the list mechanically (every `unfold`, `iunfold`, `simp only
[...]` and positional `icases` of a package fact in the callers' proofs, filtered by the defining
module), not from memory; and a package's proof-only definitions (a loop invariant) go in a module
only that proof imports, not the package's public `Defs`.

## 2026-10-28, the compactor pilot's freeze test (M2's S3 glue)

The first revision after the freeze: the frozen `v3compactor.compactableOk` and the pilot's
`EtcdServer.Compact.spec` let `Compact` run under any context, but `Compact`'s body
(`traceutil.EnsureTrace`) reads `ctx.Value(TraceKey{})` and writes to a trace it finds there; five
review rounds checked the contract against `Compact.spec`, itself an unproved `sorry`. Rule (the
reviewer's "Failure patterns"): when a contract is checked against its implementation's spec and
that spec is unproved, check it against the implementation's Go body too: every value the body
reads from an argument (a context's `Value`, a field) needs a premise.
