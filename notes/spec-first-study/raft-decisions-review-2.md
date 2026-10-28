# Review 2 of the conf-change decision switch (candidate 14 rev 2, 2026-10-28)

Target: `/home/ubuntu/.claude-E/jobs/c8379647/tmp/raft-decisions-spec.md`, **rev 2**, against review 1
(`raft-decisions-review-1.md`). Read against HEAD `14d4505fe1`, committed state (`git show HEAD:`). The worktree has
uncommitted edits to kv and `InvNodeRule`/`InvApiRule`; I ignored them. Sources read: the interim API
(`interface/Proof/go_etcd_io/raft/v3/InvNodeRule.txt`, `ConfRule.txt`, `InvNode.txt`, `NodeApiVocab.txt`, the
`unifiedSpec`s of `node.ApplyConfChange`, `node.Advance` and `MemoryStorage.CreateSnapshot`); the interim's
implementation (`Proof/go_etcd_io/raft/v3/InvApiRule.lean`); the node layer (`InvNodeChan.lean`'s `nodeCfg`/`runCfg`,
`InvApiDyn.lean`'s `nodeConfig`); the protocol's decisions (`Protocol/CfgOverlap.lean`); kv's proof (`KV__run.lean`,
`StartCluster.lean`, `Defs.lean`); `examples/kvreconf/kv.go`; `.lake/raft-fork/confchange/confchange.go`. Nothing was
built and nothing in the repository was changed.

## Verdict

**Ready to freeze.** Every Tier 1 and Tier 2 finding of review 1 is fixed in rev 2, and rev 2's changes add no new
Tier 1 or Tier 2 finding. What is left is Tier 3. Those items are wording, plus laws that can be added later without
changing a frozen statement. None blocks the freeze. Two things remain uncertain, as they were in review 1: the
protocol side ("no safety argument changes"), which I did not re-audit, and how the ghost-map camera fits `AllG`
(see §1).

## Review 1's findings at rev 2

| Finding | Status | Evidence |
|---|---|---|
| T1-1 `PolicyOk kvRule` false | **Fixed** | §2 (spec:43-51) has no `PolicyOk`. `confPolicy_alloc` has no premise on `r`. `confPolicy_decide` has the interim's per-call premise `(ofRule (r (l.take k) m e)).step m = some m'` (HEAD `InvNodeRule.txt`, `confPolicy_decide`). This is review 1's restatement (a), word for word, plus the mask `↑N' ⊆ E`. |
| T1-2 skip unusable | **Fixed** | §4 (spec:58-72) drops `nodeConfig_skipDecided` and takes `skippedIn` as a premise of both calls. This is review 1's restatement. See "§4" below. |
| T2-1 `ApplyConfChange` ambiguous | **Fixed** | spec:67-68: "`NoConfChangeIn l v.applied k` becomes `skippedIn γ l v.applied k` ...; `k` may still be above `v.applied` (kv calls it so)". |
| T2-2 token family | Stale (rev 1) | Settled further: a ghost map over an arbitrary value type is already used in raft (`ghostMapAuth g 1 (∅ : GMap w64 CfgNames)`, `InvApiRule.lean`, `nodeFounderU`), and `AllG` has `gmapViewR` (`Perennial/Ghost/All.lean`, `intF`). Uncertain: whether `ConfDecision` (a type of `ConfChangeIM`s) needs a code of its own. The `CfgNames` precedent suggests it does not. |
| T2-3 `witness` consumes the authority | **Fixed** | spec:23-24 gives the authority back. |
| T3-1 §5 step laws | Fixed | Old §5 dropped; "What stays" says `step` is as at HEAD. |
| T3-2 `PolicyOk` vs `ConfRule.Ok` | Moot | No `PolicyOk`. See N3 for `ConfRule.Ok`/`clamp`'s fate. |
| T3-3 `confDecided_agree` | Fixed | spec:25, without the authority. |
| T3-4 what leaves | Fixed, mostly | §5 lists `cluster_alloc_rule`, raft's `confPolicy`, `Membership.fold`, `opsOfRule`, `RaftLeave`; `ConfPolicy.lean` goes in `etc/api/raft.txt` (spec:38). Not named: the docstrings `Api.lean:24` and `RestartNode.lean:70` (they cite `cluster_alloc_rule`), and the rest of `ConfRule`'s rule vocabulary (N3). |
| T3-5 deferred items | Fixed | spec:78-80: `committed_confDecodes`, `nodeConfig_confAt`, `opsOf`, bootstrap log. |
| T3-6 bootstrap parenthetical | Fixed | Gone. `confPolicy_alloc` takes `ownConfDecisions γ ∅`. |
| T3-7 "only §1's laws" | Fixed | spec:38-39 names `isCommittedLogLb_agree` and `confAt_agree`. |
| T3-8 protocol section | Partly | The node-layer change is now named (spec:97-98), but it is described wrongly for `Advance` (N1). |
| T3-9 stale wording | Fixed | §2's heading says "over the authority"; "strictly more" is gone. |

## What rev 2 changed, judged

### §1: `ownConfDecisions_witness` and `confDecided_agree`

- **`witness` is right and needed.** `confPolicy_decide`'s `some d` case returns a `confDecided γ k d` the caller
  does not hold, from an invariant opened in a fancy update without a step.
  - `confDecided` is not stated `Timeless`: HEAD's `InvNodeRule.txt` has no `confDecided_timeless`, and the
    interim's `confDecidedU` is not timeless.
  - So the library cannot take the copy stored under `▷`. It takes the authority instead (which is `Timeless`,
    spec:20), strips `▷` with `◇`, and calls `witness`.
  - The equalities it needs come out under `▷` as pure facts: `▷⌜m0 = m⌝` from `confAt_agree`, and `▷ ⌜φ⌝ ⊢ ◇ ⌜φ⌝`.
  - So §2 is provable with exactly the laws given.
- **`confDecided_agree` is true after the switch.** `confDecided` becomes a persistent fragment of the client's ghost
  map (the protocol section: `reDyn` becomes the map's name). Two fragments at one key agree.
  - At HEAD it would be false: `confDecidedU` matches only up to `DecMatch`, `InvApiRule.lean:184-188`.
  - It makes `ApplyConfChange` safe against misuse. An entry that `Advance` passed as `.skip` cannot later be given
    to `ApplyConfChange`, which needs `confDecided γ k (.apply o')`, because `agree` rules out `.skip = .apply`.
- **`confAt_decided` stays true.** It does need `confDecided γ k d` to carry the facts `confDecide` checked: some
  `confAt γ k m0` with `d.step m0 = some _`.
  - So `confDecided` is the fragment together with those facts, as `confDecidedU` carries its fold facts today.
  - `confAt` is the fold of the witnessed decisions over a committed prefix.
  - Neither definition refers to the other, and `confDecide` stays a basic update `==∗` (it opens no invariant).
  - This is an implementation note, not a finding.

### §2: the per-call premise, no `PolicyOk`

- **It is sound and complete for kv.**
  - kv's call (`KV__run.lean:595-601`) keeps its premise proof `(by rw [kvRule_decide …]; exact Hkm)`.
  - The `ihave … $$ []` becomes an `imod` at `⊤`. Nothing is open there: `kv_committed_cc` was opened and closed at
    `⊤`, `:563`.
  - `StartCluster.lean:237` becomes `cluster_alloc` followed by `confPolicy_alloc` at `⊤`.
  - `kvCluster`'s `confPolicy γr.cluster kvRule` (`Defs.lean:501`) becomes the library's with `kvConfN`.
  - The namespace `N'` is the caller's choice, which is right.
- `m'` occurs only in a premise, where it is an existence claim, not a vacuous parameter. In the `some` case the
  premise is unneeded, but the caller cannot tell the two cases apart, so the premise cannot be dropped.

### §4: the `skippedIn` premise and the internal change

- **Sound.**
  - `ApplyConfChange` at `k` requires `v.applied ≤ k` and every conf entry in `[v.applied, k)` decided `.skip`.
  - `Advance` requires the same over `[v.applied, delivered.length)`.
  - So an entry decided `.apply` is never passed by `Advance`. By `agree`, an entry decided `.skip` is never applied.
  - This is what raft needs. It does not decode an entry at application, only at proposal, and a skipped entry
    leaves raft's configuration as it was.
  - kvreconf skips by not calling `ApplyConfChange` (`examples/kvreconf/kv.go:479-487`), which is `.skip`.
  - etcd skips differently: it applies a change with `NodeID` zeroed, which `confchange` ignores
    (`confchange.go:152-157`). So etcd decides `.apply` of a change whose effect is the identity, not `.skip`. The
    API allows either, so this is not a finding, and the server is untouched this stage.
- **Persistent as written.** Its conjunct `∀ e, ⌜…⌝ → confDecided …` is persistent by Iris's `impl_persistent`
  (pure antecedent, `Iris/BI/Plainly.lean:421`) and the big-sep and `∀` instances.
- **kv's glue**: one `ihave #Hsk := skippedIn_noConf … Hv.2.1` per call, at three calls:
  - `ApplyConfChange` at `:610`, from `Hv.2.1`;
  - `Advance` at `:682` and `:736`, from `HA1`.
  - kv's text is otherwise unchanged.
- **The internal bullet (spec:71-72) is half right. Tier 3 (N1).**

## Findings

No Tier 1. No Tier 2.

### Tier 3

**N1. §4's internal bullet and the protocol section describe `Advance`'s internal change wrongly.**
- **Principle.** Know the margin; this is the plan's description, not the API.
- **Evidence.**
  - At `Advance` with `L = none` the spec returns `nodeConfig n γ N v` unchanged (`node__Advance.txt`, `unifiedSpec`).
    The view does not move.
  - What moves is raft's `capplied`, past `ca`. Its invariant `NoConfIn (rsDlv rs) ca rs.capplied`
    (`InvNodeChan.lean:834`, and `runCfgLoan`'s `NoConfIn rs.delivered rs.capplied …` at `:843`) must become "every
    conf entry in `[ca, capplied)` decided `.skip`", which holds persistent `confDecided` witnesses.
  - At `ApplyConfChange` the view does move, from `v.applied` to `k + 1`, past the skipped entries. There the bullet
    is right.
- **Caller.** None: internal.
- **Restatement.** "At `ApplyConfChange`, the view moves to `k + 1`, past the skipped entries. At `Advance` it stays.
  `runCfg`'s and `runCfgLoan`'s `NoConfIn` between `ca` and `capplied` becomes 'every conf entry in that range decided
  `.skip`'."
- Also, spec:69's "(the no-snapshot case)" is inaccurate. `Advance`'s `NoConfChangeIn` premise is unconditional at
  HEAD, and kv passes `HA1` in both arms (`:682`, `:736`). Say that `skippedIn` replaces it for both `L`.

**N2. `skippedIn`'s laws for a client that does skip (kvreconf, later).**
- **Principle.** Law coverage: a client does not unfold the vocabulary.
- **Evidence.** kvreconf builds `skippedIn` one entry at a time, across Ready batches whose delivered log grows. It
  also needs `confAt` past the skips, for `confDecide` at the next conf entry and for `snapshotCert_make` (which needs
  `confAt γ l.length m`). With only `skippedIn_noConf`, `confAt_noConf` and `confAt_decided`, it must unfold
  `skippedIn` and do the induction itself. kv needs none of this.
- **Restatement.** Additive laws, which can come with kvreconf's stage:
  ```lean
  theorem skippedIn_snoc : skippedIn γ l a b ∗ (∀ e, ⌜l[b]? = some e ∧ e.isConfChange⌝ → confDecided γ b .skip)
      ⊢ skippedIn γ l a (b + 1)                                       -- (a ≤ b)
  theorem skippedIn_mono : l <+: l' → b ≤ l.length → skippedIn γ l a b ⊢ skippedIn γ l' a b
  theorem confAt_skipped : a ≤ b → b ≤ l.length →
      isCommittedLogLb γ l ∗ skippedIn γ l a b ∗ confAt γ a m ⊢ confAt γ b m
  instance : Persistent (skippedIn γ l a b)
  ```

**N3. What else of `ConfRule` leaves.**
- **Principle.** After a change, drop what existed only for what it changed.
- **Evidence.**
  - Once `Membership.fold` leaves and there is no `PolicyOk`, nothing uses the following entries of `ConfRule.txt`:
    `ConfRule.Ok`, `clamp`, `clamp_ok`, `clamp_eq`, `validated`, `validated_ok`, `Membership.fold_total`,
    `foldFrom`/`foldStep` and their laws, and `opsOfRuleFrom`/`opsOfRule_noType2`.
  - `git grep` finds no use of them outside `Proof/go_etcd_io/raft/v3/`.
  - `ConfRule` itself, `ConfDecision.ofRule` and `ccDecode` stay, because the library and kv use them.
- **Restatement.** List them under §5, either as leaving or as kept as the `ConfPolicy` library's vocabulary. Also
  name the two docstrings that cite `cluster_alloc_rule` (`Spec/go_etcd_io/raft/v3/Api.lean:24`,
  `RestartNode.lean:70`).

**N4. State the instances that the comments promise.**
- `confPolicy` is marked "-- persistent" (spec:43). kv keeps `kvCluster` as a persistent bundle (`#Hkc`,
  `StartCluster.lean:243`), so it needs `confPolicy_persistent`. Write it as an `instance`.
- After the switch, `confAt` and `confDecided` are timeless: fragments plus `isCommittedLogLb`, which is timeless
  (`InvNode.txt:30`). Exporting `Timeless` for both is cheap, and an etcd-style client that keeps witnesses in its
  own invariant would use them. This is optional; the library does not need it (see §1 above).

**N5. Protocol section.**
- The decoder already has the rejection. `CCDecision.reject`, "the application does not call `ApplyConfChange`"
  (`Protocol/CfgOverlap.lean`, U6m), with `CCDecision.step .reject s = some s`.
- So what is new on the protocol side is only that the decision map is ghost state with lower bounds, not the folding
  over skips. Saying so would make the "no safety argument changes" claim easier to check.
- I did not re-audit the protocol (uncertain, as in review 1).

## What is good

- **The design is right.** Raft's API owns no rule. The decisions are the client's ghost state (TaDa), recorded once
  per position, and only where the decision is allowed. A rule is a client library, built on public laws, with a
  namespace the caller chooses.
- **The laws are minimal and complete for the library.** The authority is exclusive and timeless; `lookup`;
  `witness`, which gives the authority back; `agree`, which needs no authority; and `confDecide`. §2 is provable from
  them, the two agreement laws and `◇`. No other law is needed.
- **§4 reuses the interim's mechanism.** Premises at the two calls, no entailment that changes a pinned ghost
  variable, and kv's case is vacuous through `skippedIn_noConf`.
- **The clients' text is unchanged.** `kv.New.spec`, `kv.KV.run.spec` and `kv_porcupine_safe` keep their statements.
  kv's glue changes by about one line per call: one at the decide site, and one at each `ApplyConfChange` and
  `Advance` call.
- **No bug in the Go code** was found, so there is no `issues/` entry.

## Ranking (by need of revision)

1. §4's internal bullet and the protocol section (N1, N5): wording only.
2. §5's list of what leaves (N3).
3. The instances (N4) and `skippedIn`'s laws (N2): additive, and can follow.
4. §1, §2, §3, "What stays", "Clients": none.

Tier 1: none. Tier 2: none. Tier 3: N1 to N5. **Ready to freeze**; folding in N1 and N3 first would cost a few
lines.
