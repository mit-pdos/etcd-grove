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
