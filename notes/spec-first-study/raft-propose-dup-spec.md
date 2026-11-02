# Candidate 15 rev 2 (S1, frozen 2026-10-29): proposals over duplicating networks, without a registry

Rev 2 (user, 2026-10-29: no `propCredit` definition; the update is wrapped in Iris's `□?γ.dup`
(`intuitionisticallyIf`), so `propCredit_false`/`propCredit_persistent` are Iris's own laws. User
approved S1 with this change.)

Rev 1 (review 1, `raft-propose-dup-review-1.md`): F1 `msgCredits_intro` depends on U7's read-credit
exchange (until then `msgCredits_none`/`_snapshot` stay); F2 every allocation fixes `γ.dup` (the flag
lives in `RaftNames`); F3 the internal plan names what splits on `dup` (tickets, index records,
`fire_one`); F4 kvreconf's update tests `op ∈ ops`, not "applied"; F5 `propCredit_true` replaced by an
unconditional `propCredit_persistent`; F6 the automatic-leave paragraph dropped (a filler carries no
ticket); F7 empty data in a dup cluster still needs `□ AU`.

Status: draft, 2026-10-29. Supersedes, in the frozen candidate 12 (`raft-node-unified-candidate.md`)
and the decisions spec (`raft-decisions-spec.md`), everything about proposals: the registry
(`ownProposals`, `proposalReg`, `proposals_register`, `proposalReg_elem`, `proposals_all`), the
registry disjunct of `sentMsg_prop`, `Propose`'s `proposalReg` premise and the `MsgProp` case of
`msgCredits_intro`. Everything else in candidates 12/14 is unchanged.

User's decision (2026-10-29): `Propose` takes only an atomic update, as on `lean`; when raft returns a
`MsgProp` it gives permission to step it once; a client on a duplicating network must make that
permission persistent, which it does by giving persistent updates when it proposes. A two-way case
on the cluster is allowed for this (explicit permission: "bifurcating proofs into two cases"), on the
condition that every dup-conditional statement is as local as possible: one spec per function and
one proof, with resources written `if dup then P else Q`; no second family.

## Changes from candidate 12/14

1. The cluster carries a client-chosen `Cluster.dup : Bool`, fixed at allocation.
2. No new definition: the update is wrapped in Iris's `□?γ.dup` (`intuitionisticallyIf`).
3. `node.Propose.spec`: `lean`'s, with its update wrapped in `□?γ.dup`. With `dup = false`
   it is `lean`'s spec exactly (`□?false U = U`).
4. `node.ProposeConfChange.spec`: today's, with its update wrapped in `□?γ.dup`.
5. New law `msgCredits_copy` (the only dup-conditional law): in a `dup` cluster a `MsgProp`'s
   credits are persistent.
6. Removed: the registry (`ownProposals`, `proposalReg` and their three laws), `ownProposals γ ∅`
   in the allocation, `sentMsg_prop` (no client uses it once copies need no witness), and the
   `MsgProp` case of `msgCredits_intro`, which becomes `msgCredits_intro : st.msg.Type' ≠ MsgProp →
   ⊢ |==> msgCredits γ N st` (today's `msgCredits_none`/`msgCredits_snapshot`; the read credit as in
   U7's receipts plan, unchanged by this candidate).

## Statements

```lean
-- the cluster (sealed, as γ.c0)
def (sealed) Cluster.dup (γ : Cluster) : Bool

-- the allocations (F2). `cluster_alloc_dec` (the unified cluster; `cluster_alloc` after U9): one more
-- argument, one more conjunct, nothing else changes
theorem cluster_alloc_dec (N : Namespace) (vs : List w64) (dup : Bool) (E : CoPset) :
    receiptBound GF ≤ 2 ^ 64 - 2 → vs ≠ [] → vs.Nodup → W64 0 ∉ vs → ↑vs.length < 2 ^ 62 →
    ⊢ |={E}=> ∃ γ, ⌜γ.dup = dup⌝ ∗ ownCommittedOps γ [] ∗ ownReadCtxs γ ∅ ∗ … (as today, without
      `ownProposals γ ∅`)
-- the old `cluster_alloc` (static; the server, `NewServerAlloc.lean:216`) and `dynamicCluster_alloc`
-- (both deleted in U9): no new argument, one more conjunct `⌜γ.dup = false⌝`
-- (internally the flag is a field of `RaftNames`, since `propTk`/`entTk` take `γ.raft`;
-- `Cluster.dup γ := γ.raft.dup`)

-- what a proposer gives raft for its proposal's commit: `□?γ.dup U` (Iris's `intuitionisticallyIf`):
-- the update itself on a network that never duplicates a `MsgProp` (`γ.dup = false`: `□?false U = U`,
-- Iris's `intuitionisticallyIf_false'`), a persistent one on a network that may (`msgCredits_copy`);
-- a persistent update meets it in either case (`□ U ⊢ □?b U`). No new definition.

/-- In a cluster allocated with `dup`, a `MsgProp`'s credits (what `Ready` returns with it, and
what `stepIn_intro` takes) are persistent: a network may step any number of copies of it. Every
other message's credits come from `msgCredits_intro`. -/
theorem msgCredits_copy (γ : Cluster) (N : Namespace) (st : MsgSt) :
    γ.dup = true → st.msg.Type' = MsgProp → msgCredits γ N st ⊢ □ msgCredits γ N st

-- (F1) after U7's read-credit exchange (a `MsgReadIndex`'s credit raft's own receipt, no longer
-- `rdCred 1`); until it lands, today's `msgCredits_none` (not `MsgReadIndex`, not `MsgProp`) and
-- `msgCredits_snapshot` stay, and a `MsgReadIndex` copy needs today's `readCredit`. Once it lands,
-- `msgCredits_copy` may drop its `MsgProp` premise (every credit is then persistent in a dup cluster).
theorem msgCredits_intro (γ : Cluster) (N : Namespace) (st : MsgSt) :
    st.msg.Type' ≠ MsgProp → ⊢ |==> msgCredits γ N st
```

```lean
def node.Propose.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (data_sl : GoSlice) (data : List w8)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗
      ownSlice data_sl data DFrac.discard ∗
      □?γ.dup (AU <{ ∃∃ ops, ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅
         <{ ∀∀ t, ownCommittedOps γ (ops ++ [⟨t, W32 0, data⟩]), COMM True }>) }}
  -- (the update as on `lean`: it never fires for `data = []`, a filler)
    n.Propose(ctx, data)
  {{ (err : GoInterface), RET #err;
      ⌜err = interface.nil⌝ ∨ errStopped err ∨ errProposalDropped err ∨ ctxErr cd err }}
  -- (stopped answers as U9a: errStopped err comes with nodeStopped n γ N)

def node.ProposeConfChange.spec : Prop :=
  ∀ n γ N id c o dq ctx cd,
  {{ isPkgInit … ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗ ownConfChangeI c dq (some o) ∗
      □?γ.dup (AU <{ ∃∃ ops, ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅ <{ ∀∀ t bs,
          ⌜MarshalsConfChange (some o) bs⌝ ∗
          ownCommittedOps γ (ops ++ opsOf [⟨t, confChangeEntryType (some o), bs⟩]), COMM True }>) }}
    n.ProposeConfChange(ctx, c)
  {{ (err : GoInterface), RET #err; ownConfChangeI c dq (some o) ∗ nodeErr cd err }}
```

`Ready`'s post (`readyRest`: each message with `sentMsg γ N id q.st ∗ msgCredits γ N q.st`),
`stepIn_intro` and `node.Step.spec` are unchanged.

## How each client uses it

- **etcd's server, examples/kv** (networks that never duplicate a `MsgProp`): allocate with
  `dup = false`, keep `⌜γ.dup = false⌝` beside `isCluster` (one pure fact), and rewrite
  `□?false U = U` at each `Propose`/`ProposeConfChange` call: their one-shot updates as on `lean`.
  Their networks step each message once, with the credits `Ready` gave.
- **examples/kvreconf** (`deliver` steps a message twice, one time in 32): allocate with
  `dup = true`. At `Cluster.do`, the request's client update goes into kvreconf's invariant under
  its encoding `op`; every `Propose(ctx, op)` call (and every retry) gives
  `□ AU(op)`: "if `op` does not occur in the committed `ops` yet, fire the client's update, else
  nothing" (F4: the update fires at commit, before any replica applies), built from the invariant
  and the persistent witness that `op` is in its table (so persistent); `applyOp`'s dedup on
  `applied[op]` (`kv.go:503-526`) agrees with it (the first occurrence linearizes).
  (F7) A dup client proposing empty data still gives `□ AU`; none does. Conf changes: `□` of its decision-recording
  update, which a second commit of the same change also satisfies (kvreconf's invariant decides
  every committed conf entry). Its network, holding `msgCredits γ N st` for a `MsgProp` from
  `Ready`, takes `□ msgCredits` by `msgCredits_copy` and steps as many copies as it likes; other
  messages' copies take `msgCredits_intro`.

## How raft's proof carries it (internal, for track A)

- Internally `msgCredits` is `rdCred γ.raft (if MsgReadIndex then 1 else 0) ∗ stTks γ.raft st`
  (`InvApi.lean:2086`): the forwarded proposal's tickets, the updates kept in raft's ticket
  invariant; for a `MsgProp`, `rdCred 0` is the unit (persistent).
- (F3) What splits on `dup`, each a local `if γ.raft.dup then … else …` in one definition, the proofs
  over them unchanged (the 12 files that only carry `entTk` along are untouched):
  - the ticket `propTk` (`Protocol/Ghost.lean`): a persistent witness of the proposal's □-update in a
    dup cluster, today's exclusive token otherwise;
  - the index record the append makes of it (`propTk_set`, `propIdx`, `Ghost.lean:1188-1213`) and the
    committed entry's ticket part of `entDataIs` (`Ghost.lean:1232`): persistent records in a dup
    cluster (one entry per committed copy), one-shot otherwise;
  - `fire_one` (`LeaderCompleteness.lean:936-959`): in a dup cluster the deposit is `□`, so firing
    leaves it in place instead of moving its slot to `fired`; otherwise as today.
  The deposited update is `□?γ.dup (AU …)`, fired through `□?b P ⊢ P`.
- The automatic leave is a filler: no ticket, it fires the standing `noopAu` (F6); nothing changes.
- `msgCredits_copy`: `rdCred 0` is the unit and, in a dup cluster, `stTks` is persistent.

