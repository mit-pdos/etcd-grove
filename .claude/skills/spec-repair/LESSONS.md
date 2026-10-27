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
