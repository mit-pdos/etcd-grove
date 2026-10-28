# The conf-change decision switch: the spec (candidate 14 rev 2, 2026-10-28)

Scratch file, never committed. Candidate 13 rev 3 §13 reconciled with the interim API
(`interface/Proof/go_etcd_io/raft/v3/InvNodeRule.txt`, the `unifiedSpec`s), with the user's authority design
(rev 1) and review `raft-decisions-review-1.md`'s fixes (rev 2). It lists exactly what the stage changes;
everything else stays.

## What stays (already in the interim API)

`isCluster`; `confAt` (persistent; `confAt_agree`, `confAt_valid`, `confAt_noConf`, `confAt_decided`);
`confDecided` (persistent); `ConfDecision := apply o | skip` and its `step` (as at HEAD); the snapshot laws
(`ownSnapsMade`, `snapMade`, `snapMade_elem`, `snapshotCert_make` with `SnapListsOk`, `snapshotCert_made`);
`nodeFounder`; `RestartNode.unifiedSpec`, `MemoryStorage.CreateSnapshot.unifiedSpec`.

## 1. Decisions: a client-owned authority (new, in `InvNodeRule`)

```lean
/-- The decisions recorded so far, by log position (exclusive; the client's, typically in an invariant). -/
def (sealed) ownConfDecisions (γ : Cluster) (D : GMap Nat ConfDecision) : IProp GF
instance : Timeless (ownConfDecisions γ D)
theorem ownConfDecisions_excl : ownConfDecisions γ D1 ∗ ownConfDecisions γ D2 ⊢ False
theorem ownConfDecisions_lookup : ownConfDecisions γ D ∗ confDecided γ k d ⊢ ⌜D !! k = some d⌝
theorem ownConfDecisions_witness : D !! k = some d →
    ownConfDecisions γ D ⊢ ownConfDecisions γ D ∗ confDecided γ k d        -- gives the authority back
theorem confDecided_agree : confDecided γ k d1 ∗ confDecided γ k d2 ⊢ ⌜d1 = d2⌝   -- without the authority

/-- Deciding an undecided committed conf entry, at the configuration before it, with an allowed decision:
one shot per position (the map grows only where it is undefined). -/
theorem confDecide (l : List LogEntry) (k : Nat) (e : LogEntry) (m m' : Membership) (d : ConfDecision) :
    D !! k = none → l[k]? = some e → e.isConfChange → d.step m = some m' →
    isCluster γ N ∗ isCommittedLogLb γ l ∗ confAt γ k m ∗ ownConfDecisions γ D ==∗
      ownConfDecisions γ (insert k d D) ∗ confDecided γ k d ∗ confAt γ (k + 1) m'
```

## 2. `ConfPolicy`: a client library over the authority (outside raft's kernel)

Raft's API mentions no rule. A client deciding by a rule uses a library module
(`Proof/go_etcd_io/raft/v3/ConfPolicy.lean`, added to `etc/api/raft.txt`), built on §1's laws plus
`isCommittedLogLb_agree` and `confAt_agree`: an invariant holding `ownConfDecisions` and, for each recorded
decision, the facts making it the rule's answer at its prefix and membership.

```lean
def (sealed) confPolicy (γ : Cluster) (N' : Namespace) (r : ConfRule) : IProp GF      -- persistent
theorem confPolicy_alloc : ownConfDecisions γ ∅ ={E}=∗ confPolicy γ N' r
/-- The recorded decision if the position is decided (the same at every caller), else decided now. The
caller shows the rule's answer allowed at `m` (per call, as in the interim API: no global premise on `r`). -/
theorem confPolicy_decide : l[k]? = some e → e.isConfChange → ↑N' ⊆ E →
    (ConfDecision.ofRule (r (l.take k) m e)).step m = some m' →
    isCluster γ N ∗ confPolicy γ N' r ∗ isCommittedLogLb γ l ∗ confAt γ k m ={E}=∗
      confDecided γ k (ConfDecision.ofRule (r (l.take k) m e))
```

## 3. Allocation without a rule

`cluster_alloc_rule N vs r` becomes `cluster_alloc N vs`: no rule; its post gives `ownConfDecisions γ ∅` in
place of `confPolicy γ r`, the rest unchanged.

## 4. Skipping decided entries: a premise of the specs (no new law)

```lean
/-- Every conf entry of `l` in `[a, b)` is decided `.skip` (persistent). -/
def skippedIn (γ : Cluster) (l : List LogEntry) (a b : Nat) : IProp GF :=
  [∗list] j ∈ List.range' a (b - a), ∀ e, ⌜l[j]? = some e ∧ e.isConfChange⌝ → confDecided γ j .skip
theorem skippedIn_noConf : NoConfChangeIn l a b → ⊢ skippedIn γ l a b     -- (kv: vacuous)
```

- `node.ApplyConfChange.unifiedSpec`: `NoConfChangeIn l v.applied k` becomes `skippedIn γ l v.applied k` (a
  separating premise); `k` may still be above `v.applied` (kv calls it so).
- `node.Advance.unifiedSpec`: `NoConfChangeIn st.delivered v.applied st.delivered.length` (the no-snapshot
  case) becomes `skippedIn γ st.delivered v.applied st.delivered.length`.
- Internally `nodeConfig`'s ghost view moves past skipped entries at the call (the specs move it, as they
  move it past normal entries today; no entailment changes a pinned ghost variable).

## 5. Leaving the API, deferred

- Leaving: `cluster_alloc_rule`, raft's persistent `confPolicy γ r` (now the library's, §2),
  `Membership.fold` and its laws, `opsOfRule`, `RaftLeave` (stage U5 restates what it needs).
- Deferred to later stages: automatic leaves (`m'.autoLeave = false` stays in `ApplyConfChange.unifiedSpec`;
  U5), joiners (U4), the bootstrap-log allocation, `opsOf` as the pure filter with
  `committed_emptyV2_joint` (U5), `committed_confDecodes`, `nodeConfig_confAt`.

## Clients

- kv: `kvCluster γr`'s `confPolicy` is the library's, `confPolicy γr.cluster kvConfN kvRule`, allocated by
  `confPolicy_alloc` from `cluster_alloc`'s `ownConfDecisions γ ∅`; its run loop's `confPolicy_decide` (same
  per-call premise as today) becomes a fancy update under `kvConfN`; its `ApplyConfChange`/`Advance` calls take
  `skippedIn` from `skippedIn_noConf`. `kv_porcupine_safe`, the results listed at U4a, and
  `kv.New.spec`/`kv.KV.run.spec`'s text unchanged (`kvCluster`'s body changes).
- The server and the other examples: untouched.

## The protocol side

From `notes/spec-first-study/raft-node-tada-decisions-feasibility.md`: `RaftNames.reDyn` (the decoder)
becomes the ghost name of the agreeing decision map; `CfgAt` persistent over a lower bound of it (about 60
sites: Ghost, LeaderCompleteness, Refinement, ReadIndex, GhostState, RefinementDyn);
`StepR`/`RInv`/`AdmFold` parameterized by the node's witnessed map, with monotonicity; the bootstrap's
decisions at allocation. Plus the node layer: `nodeConfig`'s view moved past skipped entries at
`ApplyConfChange`/`Advance` (§4). No safety argument changes: the protocol folds only decided prefixes.
