# Review 1 of the conf-change decision switch (candidate 14 rev 1, 2026-10-28)

Target: `/home/ubuntu/.claude-E/jobs/c8379647/tmp/raft-decisions-spec.md`, **rev 1**. Rev 1 replaces §1's per-position
tokens with a client-owned authority, `ownConfDecisions γ D`. This review was begun on rev 0; findings that rev 1
settles are marked **stale**, and the section "Rev 1: the authority form" judges the change. I read it against HEAD `14d4505fe1`
(committed state, `git show HEAD:`). I also read the interim API (`interface/Proof/go_etcd_io/raft/v3/InvNodeRule.txt`,
`ConfRule.txt`, `InvNode.txt`, the four `unifiedSpec`s) and candidate 13 §13 with reviews 12 and 13. I read the
feasibility study, kv's proof (`KV__run.lean`, `Reconf.lean`, `Defs.lean`, `StartCluster.lean`), `examples/kv/kv.go`,
`examples/kvreconf/kv.go` and `.lake/raft-fork/confchange`. Nothing was built, and no file in the repository was
changed.

## Verdict

**Not ready to freeze.** Rev 1's authority form is sound and sufficient (see "Rev 1"), but both Tier 1 findings
remain, untouched by rev 1. The design is right: raft's API owns no rule, decisions are one-shot and the client's, and a policy is
the client's invariant. `confDecide`, the authority, `cluster_alloc` and the `ConfPolicy` module are sound. Two
statements need fixing first:

1. **`PolicyOk kvRule` is false**, so kv cannot allocate its `confPolicy` the way the "Clients" section says.
2. **The skip mechanism (§4) cannot be used.** It works only when the skipped entry is exactly at `v.applied`, and
   nothing else moves the view over normal entries. As a `⊢` over today's `nodeConfig` it is probably also
   unprovable. kv never skips, but kvreconf and etcd do.

Both are local fixes, given below. The rest is Tier 2 or 3.

## What is good

- **TaDa, done right.**
  - Raft's API has no client-chosen parameter. The client owns the decisions: tokens at rev 0, at rev 1
    `ownConfDecisions γ ∅`.
  - A policy is an invariant in a client library (`ConfPolicy.lean`) built on public laws.
  - It covers a rule (kv, kvreconf), a sole owner (etcd's apply thread, which fires each token just before
    `ApplyConfChange`) and an out-of-band choice.
- **Faithful to concurrency.**
  - `confPolicy` is an invariant, so it is persistent and concurrent appliers share it.
  - The tokens are exclusive and timeless (`confDecideTok_excl`, `Timeless`), which the invariant needs.
- **`confDecide` is sound, and true of raft per the study.**
  - It requires a committed conf entry (`l[k]? = some e`, `isCommittedLogLb`) and the configuration before it
    (`confAt γ k m`).
  - It checks that the decision is allowed when it is recorded (`d.step m = some m'`).
  - This settles the study's one open question (its "Not checked" paragraph): validity becomes a law of recording,
    and `ApplyConfChange` takes only the recorded decision. The study's analysis (folds only over decided prefixes;
    `adj` only between committed `CfgAt`s) still matches what `confDecide` records.
  - Protocol files changed since the study's HEAD `d9cdd1e4e1`: only `Protocol/Facts.lean`, +36/−5. I did not
    re-audit it.
- **Real dependence on the token.** With `ToksFrom`/`split`/`excl`, the decision laws do not all hold with every
  predicate read as `True`: `confDecided` must agree with `confAt_decided`.
- **The library is provable.**
  - The invariant holds `confDecideToksFrom γ j`, and for each `k < j` either the token or
    `isCommittedLogLb l0 ∗ confAt k m0 ∗ confDecided k (ofRule (r (l0.take k) m0 l0[k]))`.
  - When the decision already exists, it is matched to the caller's `l, m, e` by `isCommittedLogLb_agree`
    (`InvNode.txt:100`) and `confAt_agree`.
  - Reaching `k ≥ j` takes repeated `confDecideToksFrom_split`. No infinite big-sep is needed.
- **The kv glue barely changes.**
  - The decide site (`KV__run.lean:595-601`, at HEAD) is in a WP at mask `⊤`: just above it, `kv_committed_cc` is
    opened with `⊤`. So `ihave … confPolicy_decide` becomes `imod` under `kvConfN`.
  - `confAt_decided`'s `Hs2 : applyChange … = some m2` (`:603`) still checks by definition, since `step` is
    unchanged.
  - `kvCluster` is a bundle: its body changes, and `New.spec`/`run.spec`/`kv_porcupine_safe` keep their text.
- **What is deferred is deferred with reasons**: autoLeave (U5), joiners (U4), the boot-log allocation, `opsOf`. On
  `opsOf`: no node spec uses the rule-dependent filter yet. `opsOfRule` is unused ("Nothing here is used by the
  node specs yet", `ConfRule.lean:21`), so `ownCommittedOps` keeps today's meaning.
- **No bug in the Go code** was found, so there is no `issues/` entry. (kv ignores `proto.Unmarshal`'s error,
  `kv.go:282`; its proof already shows that every committed conf entry decodes.)

## Rev 1: the authority form (`ownConfDecisions γ D`)

**The authority form is sound, and it is sufficient for this stage's clients. I prefer it to the tokens.** It needs
one shape fix (T2-3).

- **It is a standard construction, and `==∗` is provable.**
  - It is a ghost map, client-owned: the authority is `ownConfDecisions γ D`, and each `confDecided γ k d` is a
    persistent fragment.
  - `confDecide` is the insert of a persistent element where `D !! k = none`, which is a basic update.
  - Raft holds no part of the authority. That matches the study: "Raft's ghost steps never write the map"; raft
    only consumes the witnesses, at `ApplyConfChange` and `Advance`.
  - This settles rev 0's T2-2 (how the unbounded token family is built), which is now stale. One thing remains
    unchecked: registering the ghost map's functor in `AllG GF`.
- **One shot per position.**
  - The only way to grow `D` is `confDecide`, which requires `D !! k = none`.
  - A position already decided has `D !! k = some _`, by `ownConfDecisions_lookup` applied to its witness.
  - `ownConfDecisions_excl` keeps a single authority.
  - No law shrinks or overwrites `D`.
- **Agreement.**
  - Holding the authority gives `confDecided γ k d1 ∗ confDecided γ k d2 → d1 = d2`: `ownConfDecisions_lookup`
    twice.
  - A client without it (a replica that only has witnesses) has no agreement law. T3-3 stands, but is weaker: add
    `confDecided_agree` unconditionally (true of the fragments), or record that a client gets agreement only through
    the authority.
- **Concurrent appliers that must find an existing decision.**
  - `confPolicy`'s invariant holds `ownConfDecisions γ D`. Beside it, for each `(k, d) ∈ D`, it holds the persistent
    facts that make `d` the rule's answer: a committed `l0`, `confAt γ k m0`, `d = ofRule (r (l0.take k) m0 l0[k])`.
  - `confPolicy_decide` case-splits on `D !! k`.
    - `none`: `confDecide`. Its premise `step` is the gap T1-1 is about.
    - `some d`: the recorded `d`, matched to the caller's `l, m, e` by `isCommittedLogLb_agree` and `confAt_agree`.
  - So two replicas applying the same entry concurrently both obtain the same decision. This is provable from §1.
- **Strength against the tokens.**
  - Each can be built on the other through a client invariant, so neither is strictly stronger (the spec claims
    "strictly more").
  - From the authority: per-position tokens are an invariant holding the authority plus the client's own tokens.
  - From the tokens: lookup is an invariant holding the tokens plus a ghost map of the client's own.
  - The authority is the simpler base, and it drops `ToksFrom`/`split`. What it gives up is handing one position's
    permission to a thread without an invariant. No client of the stage or the next does that: etcd's apply thread
    owns the whole authority.
  - Locality is fine: the authority is the footprint of deciding.

## Findings

### Tier 1

**T1-1. `ConfRule.PolicyOk kvRule` is false, so kv cannot call `confPolicy_alloc` (§2, "Clients").**
- **Principle.** Sound, and complete for a named caller.
- **Evidence.**
  - `kvRule := fun _ _ e => ccDecode e` (`Defs.lean:461`).
  - `PolicyOk r` quantifies over **every** valid `m` and **every** `e`.
  - Take `m = Membership.simple {1}` (valid) and `e` a type-1 entry decoding to `RemoveNode 1`. `confchange`
    refuses it: "removed all voters", `.lake/raft-fork/confchange/confchange.go:170-171`. The API's own law says so
    too: `Membership.applyChange_removeVoter` needs `GMap.delete id vs ≠ ∅` (`InvNode.txt:352-355`).
  - So `(apply o).step m = applyChange o m = none` (`ConfDecision.step`, `ConfRule.lean:239-241`). An `AddNode`
    past `2^62` ids fails the same way (`memApply` is `ccStepB`, `InvApiDyn.lean:73-78`).
  - The spec's reason, "a RemoveMember of a non-voter keeps `kvMembership` valid", holds only of the entries kv's
    invariant commits (`RmReqs`) at `kvMembership`, not of every `m` and `e`.
  - The interim's `confPolicy_decide` deliberately had no rule premise ("No premise on the rule: a decision is taken
    only where its result is a membership", `InvNodeRule.lean`, `cluster_alloc_rule`'s docstring). It had a
    per-call `step` premise instead. Candidate 14 changed that without the stage needing it.
- **Caller.** `StartCluster.lean:237` (`cluster_alloc_rule … kvRule`), which becomes `cluster_alloc` followed by
  `confPolicy_alloc`; and through it `kv_porcupine_safe`.
- **Restatement.** Either fix works; (a) is the minimal reconciliation.
  - (a) Keep the interim's per-call premise, and drop `PolicyOk` and its premise on `confPolicy_alloc`:
    ```lean
    theorem confPolicy_alloc : ownConfDecisions γ ∅ ={E}=∗ confPolicy γ N' r
    theorem confPolicy_decide : l[k]? = some e → e.isConfChange →
        (ConfDecision.ofRule (r (l.take k) m e)).step m = some m' → ↑N' ⊆ E →
        isCluster γ N ∗ confPolicy γ N' r ∗ isCommittedLogLb γ l ∗ confAt γ k m ={E}=∗
          confDecided γ k (ConfDecision.ofRule (r (l.take k) m e))
    ```
    kv's call is unchanged (`(by rw [kvRule_decide …]; exact Hkm)`, `KV__run.lean:600`). This is provable: if the
    entry is already decided, the stored decision is returned; otherwise the caller's premise feeds `confDecide`.
  - (b) Keep `PolicyOk`, but say kv switches to `kvRule.clamp` (`ConfRule.clamp_ok`; `kvRule_decide` then needs
    `m.Valid`, via `ConfRule.clamp_eq`). In that case reuse `ConfRule.Ok` rather than a new `PolicyOk` (T3-2).

**T1-2. The skip mechanism cannot be used: `nodeConfig_skipDecided` only at `v.applied`, and no law over normal
entries (§4).**
- **Principle.** Complete for every caller; nothing of §13 dropped without a reason.
- **Evidence.**
  - Today's API has **no** `nodeConfig` law (`grep nodeConfig interface/Proof/go_etcd_io/raft/v3/*.txt`: only the
    definition, `InvNode.txt:251`). The view moves only through specs:
    - `ApplyConfChange` sets `applied := k + 1`, over a range `NoConfChangeIn l v.applied k`;
    - `Advance` with `L = none` returns `nodeConfig v` unchanged;
    - `Advance` with a snapshot moves it to the snapshot index;
    - `RestartNode` starts it at `⟨0, …⟩`.
  - Candidate 12/13 had `nodeConfig_skip` for normal entries (candidate 13 file `:408-409`; §13.3 "stays"). The
    interim never had it, and candidate 14 does not restore it.
  - So a skipped entry at `j` with normal entries in `[v.applied, j)` cannot be passed:
    - `nodeConfig_skipDecided` needs `l[v.applied]` to be that entry;
    - `ApplyConfChange` needs an `.apply`;
    - `Advance`'s premise `NoConfChangeIn st.delivered v.applied st.delivered.length` excludes the entry at `j`.
  - That is the ordinary case for a client that skips. kvreconf's `applyEntry` applies normal ops, then
    `applyConf` rejects (`examples/kvreconf/kv.go:452-487`). etcd's `shouldApplyV3 = false` path does the same.
  - The `⊢` is probably also unprovable as stated (uncertain: I did not try).
    - `nodeConfig` holds the half `dghostVar γn.cap ½ (ca, cfg)` at exactly `ca = v.applied`
      (`InvApiDyn.lean:375-378`, `InvNodeChan.lean:808-811`). The other half is on the driver's side.
    - An entailment cannot change `ca`. It would hold only after redefining `nodeConfig` with `v.applied` ahead of
      `ca` over skipped entries, and the spec does not state that obligation.
- **Caller.** Not kv in this stage (`kvRule` never yields `.skip` on a committed entry). It is the reason the law
  exists: kvreconf (`kv.go:485-487`) and the server's skip path.
- **Restatement.** Use the spec's own first alternative: premises at the calls, the interim's mechanism, with no law
  that moves the view.
  ```lean
  /-- every conf entry in `[a, b)` of `l` was decided `skip` -/
  def skippedIn (γ) (l : List LogEntry) (a b : Nat) : IProp GF :=
    [∗list] j ∈ List.range' a (b - a), ∀ e, ⌜l[j]? = some e ∧ e.isConfChange⌝ -∗ confDecided γ j .skip
  theorem skippedIn_noConf : NoConfChangeIn l a b → ⊢ skippedIn γ l a b     -- (kv's case)
  ```
  - In `ApplyConfChange.unifiedSpec`, replace `NoConfChangeIn l v.applied k` with the premise `skippedIn γ l
    v.applied k`.
  - In `Advance.unifiedSpec`, replace `NoConfChangeIn st.delivered v.applied st.delivered.length` with
    `skippedIn γ st.delivered v.applied st.delivered.length`. Its post with `L = none` stays `nodeConfig v`: the
    client's `confAt` past the skips comes from `confAt_decided`.
  - Drop `nodeConfig_skipDecided`.
  - Alternatively, keep a law in the range form, `v.applied ≤ k → NoConfChangeIn l v.applied k → l[k]? = some e →
    e.isConfChange → … ⊢ nodeConfig {v with applied := k + 1}`, and state the `nodeConfig` redefinition it needs.
    That is more proof work, and a second mechanism.

### Tier 2

**T2-1. §4's text is ambiguous about `ApplyConfChange` and would break kv if read as a change.**
- **Evidence.** "The stage keeps the spec at `k = v.applied` and lets the law move the view" reads as narrowing
  `ApplyConfChange` to `k = v.applied`. kv calls it with `k > v.applied` and passes the range
  (`KV__run.lean:613-615`: `Hv.1`, `Hv.2.1`). With no law over normal entries (T1-2), kv could not reach
  `k = v.applied`. "What stays" says the spec's shape is unchanged.
- **Restatement.** Say explicitly which premise `ApplyConfChange` has after the stage: unchanged, or `skippedIn`
  per T1-2.

**T2-2. [stale at rev 1] How the unbounded token family is built, and why `confDecide` is a basic update `==∗`.**
Settled by the authority form (see "Rev 1").
- **Evidence.** The study does not construct the family ("`decTok γ i` is allocated with the cluster"). A `==∗`
  rules out an authority kept in raft's invariant (that would need `|={E}=>`, `↑N ⊆ E`). Lean Iris has a camera
  that fits (`Iris/Algebra/ReservationMap.lean`, and discrete functions in `Algebra/Functions.lean`). Whether it is
  registered in `AllG GF` is uncertain: I did not check.
- **Restatement.** One sentence in the spec: the camera, and that `confDecided`/`confAt` are fragments of it (so
  `==∗` is provable). Or make `confDecide` `={E}=∗` with `↑N ⊆ E`; kv calls it at `⊤`, so either is usable.

**T2-3. `ownConfDecisions_witness` consumes the authority (rev 1).**
- **Principle.** Law coverage, and the shape of the existing API.
- **Evidence.**
  - `D !! k = some d → ownConfDecisions γ D ⊢ confDecided γ k d` loses the exclusive authority, so a client holding
    it in an invariant cannot close the invariant again.
  - Lean's `ihave` keeps the hypotheses only for a pure result. `ownConfDecisions_lookup` is pure, like
    `snapMade_elem`, whose `Hown` is reused at `Reconf.lean:189-198`. `witness` is not pure.
  - The API's precedent returns the authority: `ownCommittedOps_get_lb : ownCommittedOps γ ops ⊢ ownCommittedOps γ
    ops ∗ …` (`InvNode.txt:50-51`).
  - `ConfPolicy` can avoid the law by storing the witnesses `confDecide` returns, so this is not Tier 1. But an
    etcd-style sole owner that re-reads a decision would hit it.
- **Restatement.**
  `D !! k = some d → ownConfDecisions γ D ⊢ ownConfDecisions γ D ∗ confDecided γ k d`.

### Tier 3

**T3-1. §5 is a candidate-13 leftover not reconciled with HEAD.**
- `ConfDecision.step` at HEAD is unfiltered (`ConfRule.lean:239-241`), and `Membership.applyChange_valid` exists
  (`InvNode.txt:323`). Review 13 N4 assumed it had been deleted. `memApply` is `ccStepB`, which already bounds ids
  below `2^62`.
- So `step_skip` and `step_apply` are `rfl` from the exposed definition, `step_apply`'s `m'.Valid` premise is
  unneeded, and `applyChange_valid_lt` is not needed at all, not just "left out".
- Say `ConfDecision.step` stays unfiltered (so N11's `Decidable` is moot). Drop §5, or keep `step_apply` without
  `m'.Valid`.

**T3-2. `PolicyOk` duplicates `ConfRule.Ok`.**
- Given `step_skip`, `PolicyOk r ↔ r.Ok`.
- If (b) of T1-1 is chosen, reuse `ConfRule.Ok`, with `clamp`/`clamp_ok`/`clamp_eq`/`validated` (`ConfRule.txt`):
  that is kvreconf's `validConf` rule already.

**T3-3. `confDecided_agree` (§13.2) was dropped without a reason.**
- Rev 1 gives agreement only to a client holding the authority (lookup twice).
- Neither the interim nor candidate 14 has the unconditional law. In the interim it would be false: `DecMatch` decides up to
  `ccV2Of`. After the switch it is true and cheap.
- A client with an out-of-band policy may want it. No client of this stage needs it.
- Add it, or list it as deferred.

**T3-4. Say what leaves the API.**
- After the switch, `Membership.fold`/`foldStep`/`foldFrom`, `RaftLeave`, `opsOfRule`, and `ConfRule.toDec` (not
  exposed, but used by the protocol) exist only for the rule (§13.1 removes them). `cluster_alloc_rule` disappears.
- The spec should list them as removed, or as kept only as the `ConfPolicy` library's vocabulary: "drop what existed
  only for what it changed".
- Also: add `ConfPolicy` to `etc/api/raft.txt` (an API change); `Api.lean:23-24`'s docstring names
  `cluster_alloc_rule`.

**T3-5. The other §13 items absent from the stage should be listed as deferred.**
- `committed_confDecodes` is needed by kvreconf, whose `applyEntry` panics on a non-decoding entry (`kv.go:458-466`).
  kv has its own `kv_committed_cc`.
- `nodeConfig_confAt` is used by the server, per review 13's L1 row.
- Name both under §6.

**T3-6. `confPolicy_alloc`'s bootstrap parenthetical** ("`[∗list] k ∈ range k0, confDecided γ k (ofRule (r …))`")
is not a statement. The membership and prefix at each `k` are unnamed. Drop it for this stage (`k0 = 0`) and leave
it to the boot-log stage.

**T3-7. "Built only on §1's laws" is slightly off.** The library also needs `isCommittedLogLb_agree` and
`confAt_agree`. Both are public, so this is only a wording fix.

**T3-8. Protocol section.**
- It understates the work: `reDyn` appears in 15 files under `Proof/go_etcd_io/raft/v3/` at HEAD (the study counted
  74 occurrences in 19), and there are about 60 `CfgAt` sites, plus `StepR`'s monotonicity in the map.
- It should name the `nodeConfig`/`Advance` internal change that T1-2's fix implies: the driver's "moved `cidx` past
  `ca` over no conf entry" becomes "over no conf entry not decided `skip`".


**T3-9. Rev 1 left stale wording.**
- §2's heading still says "a client library over the tokens".
- §1's docstring says the authority "gives the client strictly more"; each form is a layer on the other ("Rev 1").
- `confPolicy_alloc`'s bootstrap comment takes `D0` "the rule's", but in this stage `D0 = ∅`; see T3-6.

## Reconciliation with §13

| §13 item | In candidate 14? | Verdict |
|---|---|---|
| Tokens, split, excl, timeless | Rev 1: replaced by the authority (`excl`, `timeless`, `lookup`, `witness`) | The user's change. Sound, and an equivalent base (see "Rev 1"). |
| `confDecide` | Yes, §1 | Faithful. |
| `confAt_*` | Kept in the interim's forms | Fine: N10 applied, `confAt_valid` without `isCluster`. |
| `ConfPolicy` library | Yes, §2 | Changed: the per-call premise was replaced by `PolicyOk`. False for kv (T1-1). |
| `cluster_alloc` without a rule | Yes, §3 | Faithful for founders. |
| `nodeConfig_skipDecided` | Yes, §4 | Taken over, but `nodeConfig_skip` was dropped silently (T1-2). |
| Step laws | Yes, §5 | Unneeded at HEAD (T3-1). |
| `confDecided_agree` | No | Dropped without a reason (T3-3). |
| `committed_confDecodes` | No | Not stated as deferred (T3-5). |
| `nodeConfig_confAt` | No | Not stated as deferred (T3-5). |
| `committed_emptyV2_joint`, `opsOf` | Deferred to U5 | Reason given. |
| `ApplyConfChange`'s `confDecided` premise and the two `applyChange` equalities | Kept (interim already) | Faithful. |
| Server text (N5/N6) | Server untouched this stage | Fine. |

## Ranking (by need of revision)

1. §4, the skip mechanism with `ApplyConfChange`/`Advance`'s premises (T1-2, T2-1).
2. §2, `ConfPolicy`'s `PolicyOk` and `confPolicy_alloc` (T1-1, T3-2, T3-6, T3-7).
3. §1, the authority's laws: `witness`'s shape and unconditional agreement (T2-3, T3-3). T2-2 is stale.
4. §5, the step laws (T3-1).
5. The lists of removed and deferred items, and the protocol summary (T3-3, T3-4, T3-5, T3-8).
6. §3, `cluster_alloc`: none.
7. "What stays": none, beyond T2-1.

Tier 1: T1-1, T1-2 (both unchanged by rev 1). Tier 2: T2-1, T2-3 (T2-2 stale). Tier 3: T3-1 to T3-9.
