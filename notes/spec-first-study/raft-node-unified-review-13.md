# Review of the unified node-API candidate 13 (rev 2), round 13

Reviewer: a fresh spec reviewer, 2026-10-28. Read-only: nothing in the repository was changed.

## What was reviewed

- **Target**: `/home/ubuntu/.claude-E/jobs/c8379647/tmp/raft-unified-candidate-13.md`, §13.1-13.4 at revision 2
  (the "rev 2" bullets read hardest), then every candidate-12 statement that §13.3 changes.
- **Previous round**: `notes/spec-first-study/raft-node-unified-review-12.md` (L1-L9), each one checked below.
- **Feasibility study**: `notes/spec-first-study/raft-node-tada-decisions-feasibility.md`, which is identical to the
  copy in the job's `tmp/`.
- **Rubric**: `/home/ubuntu/etcd-grove/.claude/skills/spec/PRINCIPLES.md`. The worktree has no `spec/` skill. I
  used the main checkout's copy.
- **Today's API**, read at `d9cdd1e4e1` with `git show`: `interface/Proof/go_etcd_io/raft/v3/{InvNode,NodeApiVocab,ConfRule,ApiVocab}.txt`
  and `interface/Spec/go_etcd_io/raft/v3/node__{Propose,ProposeConfChange,ApplyConfChange}.txt`.
- **Protocol**, at `d9cdd1e4e1`: `Protocol/Ghost.lean:1000-1100` (`Filler`, `propDataIs`).
- **Go**:
  - raft at `.lake/raft-fork` `565c2bd`: `raft.go:737-763`, `raft.go:1320-1372`;
  - kvreconf: `examples/kvreconf/kv.go:225-241,480-495`;
  - kv: `examples/kv/kv.go:265-295`;
  - etcd's `etcdserver/server.go:1945-1961,2030-2110`.
- **Clients' proofs**:
  - kv: `Defs.lean:250-285`;
  - server: `InvCfgView.lean:1-76`, `InvRest.lean:55-110`.
- **`HEAD` has moved** to `0f4e1b41e8`. It rewords kvreconf's `validConf` comment, which closes the Go part of L6.
- **Not run**: lake build, lean-check, Go tests.

## Summary

The decision design is right and stays TaDa: one-shot tokens per position, owned by the client, and persistent
agreeing records. Rev 2 fixes the two Tier-1 findings of round 12:
- L1: `committed_emptyV2_joint` is true of Go. I re-derived it from `raft.go:1344-1361` and `pendingConfIndex`,
  including the case where a client applies a conf change ahead of `Advance`.
- L2: the entry premises now sit outside the turnstile.

It also mostly fixes L3, L4, L6 and L8. Two statements are still malformed, and one of them repeats L2's mistake:
- **N1**: `confPolicy_decide` has `e` free and no committed-entry premise. As written it is false.
- **N2**: `nodeConfig_skipDecided` puts the `IProp` `confDecided` among the pure premises.

**The design is ready to freeze; the text is one small revision away.** Fix N1 and N2 (each a one-line
restatement), and preferably N3 and N4.

- **Tier 1 (1)**: N1.
- **Tier 2 (3)**: N2, N3, N4.
- **Tier 3 (7)**: N5-N11, which include L7 and L9 (still open) and the rest of L6.

No bug in the verified Go code was found.

## Previous findings (round 12)

| | Status at rev 2 | Evidence |
|---|---|---|
| L1 | **Fixed.** | `committed_emptyV2_joint` is true of Go: see "What is good". It is usable by the server (from `nodeConfig_confAt` at the entry and `srvCfgOk`'s simple membership) and by kv. |
| L2 | **Fixed** for `confAt_normal`/`confAt_decided`. **Repeated** in the new `confPolicy_decide` (N1). | — |
| L3 | **Fixed.** | The AU still binds `bs` (today's `node__ProposeConfChange.txt:14-16`), so `ops ++ opsOf [⟨t, ty, bs⟩]` is decided where raft's proof knows `bs`. The obligation on `Filler` is listed; see N8. |
| L4 | **Fixed.** | The bootstrap change is named and matches `BootLog`'s `⟨W32 0, id, ctx, W64 0⟩`, `NodeApiVocab.txt:22-33`. `confAt γ k c0` holds for `k ≤ boot.length`. The token family is unbounded, with a split law. The instances are listed. Nits in N9. |
| L5 | **Partly fixed.** | `ConfPolicy` exists, but its law is malformed (N1) and its `f` cannot express etcd's decision (N3). |
| L6 | **Mostly fixed.** | The `kv.go` comment is fixed at `HEAD` `0f4e1b41e8`. Still open: whether §6's `shouldApplyV3` scope restriction survives (N6). |
| L7 | **Open.** | §13.3's last bullet still says etcd decides "deterministic over its replicated membership store, fired the same way" (N5). |
| L8 | **Fixed.** | The `ApplyConfChange` reason is reworded, the garbled sentence is gone, and `isEmptyV2` is `Decidable`. |
| L9 | **Open.** | Not recorded in §6 (N7). |

## What is good

- **`committed_emptyV2_joint` is true of Go and complete for the clients that need it.**
  - **The leader appends an empty V2 only at a joint configuration.** An empty `ConfChangeV2` reaches the log only
    through `stepLeader`'s `MsgProp` (the client's, or `appliedTo`'s at `raft.go:742-763`, which goes through
    `r.Step`). There it is accepted only with `!alreadyPending && alreadyJoint` (`raft.go:1344-1361`, given
    `DisableConfChangeValidation = false`).
  - **The leader's tracker is the configuration at the appended position.** `alreadyPending` false means every
    conf entry of the leader's log is at or below `raftLog.applied`. `pendingConfIndex` covers the entries the
    leader inherited (`becomeLeader`) and those it accepted (`:1361`). So between `applied` and the new position
    there are only normal entries.
  - **The tracker equals `confAt` at `applied`.** It moves only through `ApplyConfChange` (with the decided effect),
    through a skip (no change), or through a snapshot at `appliedSnap`. A client that has applied a conf entry
    ahead of `Advance` has also left `pendingConfIndex > applied`, so the leader refuses the proposal.
  - **Usable by the server, conf batches included.** The server never builds a joint configuration. Its apply
    thread holds `nodeConfig` for a batch with a conf entry (`InvCfgView.lean:5-9`), and `confAt` is persistent,
    so the raft loop can hand over the facts for the normal batches. That is enough to exclude the panic at
    `server.go:1956-1961`.
- **Decisions are unrelated to the entry's bytes, and that is sound.**
  - `confDecide` lets a client record `.apply o` for any `o` with `d.step m = some m'`. Raft's Go never compares
    the change passed to `ApplyConfChange` with the entry.
  - Safety rests only on each step being a `confchange` step (`fold_adjacent` for an arbitrary `dec`, as round 12
    checked).
  - So the API puts no constraint on the decision beyond the protocol's need. That is the TaDa point, and an
    out-of-band decider is admitted.
- **No mask, no client predicate.**
  - `confDecide` is a plain `==∗`: per position it needs only a one-shot ghost cell plus the persistent fold
    witness.
  - No library predicate takes a client policy ("TaDa, not HoCAP").
- **`ApplyConfChange` and `Advance` stay local.** They take only the persistent `confDecided`/`confAt` (via
  `nodeConfig`), not the client's invariant.
  - `ApplyConfChange` keeps `deliveredLogLb l`, `l[v.applied]? = some e` and `e.isConfChange`, which the protocol's
    `applyConf` needs (the entry below this node's own commit, `StepR.lean:437-447` per the study). §13.3 replaces
    only the rule premise, correctly.
- **Stopped replicas need no decision.** A kvreconf replica whose `ApplyConfChange` answered `nil` holds
  `nodeStopped` and a `nodeConfig` that has not moved. It never has to fire a token for the rest of its batch: the
  stopped precondition `P ∨ nodeStopped` takes no decision.

## Findings

### Tier 1

**N1 [spec]. `confPolicy_decide` is false as written (L2 again).** (Sound.)

- **Evidence.**
  - In `confPolicyInv γ f ∗ isCommittedLogLb γ l ∗ confAt γ k m ={E}=∗ confDecided γ k (f m e)` the entry `e` is
    free, and nothing ties `k` to `l`.
  - Take `e1, e2` with `f m e1 ≠ f m e2`. The law gives both decisions, and `confDecided_agree` derives `False`.
  - With `k ≥ l.length` it would fire a token for a position not yet committed. Even with `l[k]? = some e`, a normal
    `e` would need a decision that `confDecide` cannot make (its premise `e.isConfChange`).
  - The law is optional and outside raft's API, but §13.2 says kvreconf, kv and the server use it.
- **Restatement.**

  ```lean
  theorem confPolicy_decide : l[k]? = some e → e.isConfChange → ↑N_pol ⊆ E →
      confPolicyInv γ f ∗ isCluster γ N ∗ isCommittedLogLb γ l ∗ confAt γ k m ={E}=∗ confDecided γ k (f m e)
  theorem confPolicy_alloc : (∀ m e, m.Valid → ∃ m', (f m e).step m = some m') →
      confDecideToksFrom γ k0 ={E}=∗ confPolicyInv γ f          -- persistent (an invariant)
  ```

  Fix the domain of `f` together with N3.
- **Affects**: the apply step of kvreconf (`kv.go:485-489`) and of kv (`kv.go:280-283`).

### Tier 2

**N2 [spec]. `nodeConfig_skipDecided` is ill-typed.** (Sound, well-formed.)

- **Evidence.** `… → confDecided γ v.applied .skip → nodeConfig v ∗ deliveredLogLb l ⊢ …` uses an `IProp` as a
  `Prop` premise.
- **Restatement.**

  ```lean
  theorem nodeConfig_skipDecided : l[v.applied]? = some e → e.isConfChange →
      confDecided γ v.applied .skip ∗ nodeConfig n γ N v ∗ deliveredLogLb n γ N l ⊢
        nodeConfig n γ N { v with applied := v.applied + 1 }
  ```

- **Affects**: kvreconf's rejection (`kv.go:485-487`), and etcd's `shouldApplyV3 = false` path if it ever enters
  scope (N6).

**N3 [spec text; preference: one general spec]. `ConfPolicy`'s `f : Membership → LogEntry → ConfDecision` cannot
express etcd's decision.** (Complete.)

- **Evidence.**
  - The server decides on the member buckets the log before the entry leaves: `srvDec` uses
    `ccRaftEff (restModel c0 boot (withIdx pre)).bk` (`InvCfgView.lean:71-74`).
  - That rejects re-adding a removed id and peer-URL clashes (`ccValidM`, `InvRest.lean:65-70`). Raft's
    `Membership` records neither. So the server's `f` would need the prefix.
- **Restatement.** Either:
  - take `f : List LogEntry → Membership → LogEntry → ConfDecision` (round 12's L5), the law concluding
    `confDecided γ k (f (l.take k) m e)`; or
  - drop the server from "kvreconf, kv and etcd's server use it" and say it owns the tokens outright and fires at
    `applyConfChange` (N5).

  The second is simpler and is what the server's proof can do.

**N4 [spec; every premise has a source]. No law lets a client prove `(.apply o).step m = some m'`.**

- **Evidence.**
  - `ConfDecision.step` filters on the sealed `Membership.Valid`. A client firing `.apply o` must show
    `m'.Valid` from what it checked:
    - kvreconf: `err == nil && len(after) < 2^62` (`kv.go:241`);
    - kv: a `RemoveNode` of a non-voter;
    - the server: its validated `V1` change, or the zeroed one.
  - Today's `Membership.applyChange_valid` (`InvNode.txt:323`) was deleted (K3: false at the size bound). §4b's
    size law gives only `len(prs) = m.ids.size`.
  - No law turns "`applyChange` succeeded from a valid `m` and the result has fewer than `2^62` ids" into
    `m'.Valid`, and none says the leave applies exactly at joint configurations. §13.2's `committed_confDecodes`
    docstring asserts the latter without a law.
  - The gap predates §13 (candidate 12's `clamp` needed the same fact), but §13 makes `confDecide` the only way to
    a configuration change, so every client now meets it.
- **Restatement.** Add to `InvNode`:

  ```lean
  theorem Membership.applyChange_valid_lt : m.Valid → Membership.applyChange o m = some m' →
      m'.ids.size < 2 ^ 62 → m'.Valid
  theorem ConfDecision.step_apply : (ConfDecision.apply o).step m = some m' ↔
      Membership.applyChange o m = some m' ∧ m'.Valid
  theorem ConfDecision.step_skip : ConfDecision.skip.step m = some m
  ```

  The first is uncertain: `Valid` is sealed, and I did not check that `confchange` keeps "a voter" in the incoming
  half and keeps ids nonzero. It does skip `NodeID` 0, and it refuses "removed all voters". Optionally add
  `applyChange_leave : m.Valid → (Membership.applyChange (.v2 .empty) m).isSome ↔ m.isJoint`.
- **Affects**: kvreconf's `validConf` result, kv's `RemoveMember`, the server's `applyConfChange`.

### Tier 3

**N5 [spec text]. L7 is still open.**
- §13.3's last bullet keeps "deterministic over its replicated membership store, fired the same way".
- The server allocates the cluster (`NewServerAlloc.lean:216`) and its apply thread is the only applier. It keeps
  the tokens and fires `.apply (ccRaftEff bk cc)` just before `s.r.ApplyConfChange` (`server.go:2036`, `:2052`).
  No determinism invariant is needed.
- Say this.

**N6 [spec text]. §6's `shouldApplyV3` restriction.**
- §13.3 says §6's first bullet is "replaced by the decisions" and does not say whether the restriction
  "`shouldApplyV3 = false` skips `ApplyConfChange`, sound only without restarts" survives.
- Under TaDa the skip is just a `.skip` decision the server records, so the restriction is no longer a raft-API
  premise. It is the no-restart scope, since a replay would meet a token already fired before the crash.
- Reword the bullet to say this.

**N7 [know the margin]. L9 is still open.** A client's explicit `ConfChangeV2{}` is now a filler, so no client
learns from `ownCommittedOps` that its leave committed. None needs it (`reconf.go:85-92`; kv and etcd propose no
V2). Record it in §6.

**N8 [obligation: record it].** Moving empty V2s back into `Filler` reverses the protocol's 2026-10-27 change.
- `Ghost.lean:1014-1021` says an empty `ConfChangeV2` stopped being a filler "whose decoding, `ccDecodeV2`, is
  opaque, so that no law could tell a committed filler normal".
- `ccDecodeV2_nil` removes that reason. `propDataIs none` needs `CCDecodes 2 []`, which the axiom gives.
  `ccPropArg`'s disjunction (`ApiVocab.txt:40-46`) is decided on `bs`.
- So the change is local. Record it in `decisions.md` as superseding that entry, not silently.

**N9 [spec nits].**
- `confDecideToksFrom` is used but not declared in §13.2's block. Declare it sealed, with `Timeless`.
- The bootstrap post's `ps[k]`/`ctxs[k]` over `range boot.length` needs bounds. Use
  `[∗list] k ↦ id ∈ ps, ∃ ctx, ⌜ctxs[k]? = some ctx⌝ ∗ confDecided γ k (.apply (.v1 ⟨W32 0, id, ctx, W64 0⟩))`.
- `msgCredits_intro`'s `opsOf st.ents` should be `opsOf (strip st.ents)`.

**N10 [size; no unneeded premise].** `confAt_decided` does not need its `l[k]? = some e → e.isConfChange →` premise
or `isCommittedLogLb`, since `confDecided` exists only at committed conf entries:
`confAt γ k m ∗ confDecided γ k d ⊢ ∃ m', ⌜d.step m = some m'⌝ ∗ confAt γ (k + 1) m'`. Also write out
`committed_confAt`, which is a derived law (an induction from `confAt γ 0 c0`), or drop it.

**N11 [know what it rests on].**
- `ConfDecision.step`'s `Option.filter Membership.Valid` needs a `Decidable` instance for a sealed `Prop`. Either
  export the instance (the tester can then evaluate `confDecide`'s premise) or write `step` with
  `if Membership.Valid m' then …` under `Classical`, and say so.

## Answers to the brief

- **Wrong (false of Go or unprovable).** N1, in the optional client library. Nothing in raft's API itself is false
  of Go at rev 2: `committed_emptyV2_joint` checks out.
- **Malformed.** N2 (ill-typed).
- **Weak, or unusable by a named client call.**
  - N3: the server cannot use `ConfPolicy`, but has a better route, N5.
  - N4: kvreconf, kv and the server cannot discharge `confDecide`'s `step` premise from what they check without a
    validity law.
- **Too strong.** N10's unneeded premise.
- **Leaky.** None. The vocabulary (`ConfDecision`, `confAt`, `confDecided`, tokens) names nothing of the
  implementation, and `RaftNames.reDyn` and `CfgAt` stay internal.
- **Ready to freeze?** The design is. Freeze after N1 and N2 (one line each), with N3 and N4 preferably in the same
  revision. Tier 3 can follow during implementation.

## Ranking (by need of revision)

The only target is §13 together with the candidate-12 statements it changes. Within it:
1. `ConfPolicy`'s laws (N1, N3);
2. `nodeConfig_skipDecided` (N2);
3. the `Membership` validity laws behind `ConfDecision.step` (N4);
4. §13.3's server text and §6 (N5, N6, N7);
5. nits (N8-N11).

`confDecide`, `confAt_*`, `committed_emptyV2_joint`, `cluster_alloc`'s post, `ApplyConfChange`, `Advance`,
`snapshotCert_*` and `ProposeConfChange` need no change beyond N9 and N10.

No bug in the verified Go code was found, so there is no `issues/` entry.
