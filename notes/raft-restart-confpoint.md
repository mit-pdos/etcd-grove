# Raft restart with a configuration point past the stored commit (design, 2026-11-24)

Design note only: no Lean changed, nothing built. Context: `notes/etcd-dist-d6.md`, "T4 round 4",
the entry "step 3 (the configuration point `a' = min |A₀| σ.commit`): does not work". Go sources
cited: raft at `RAFT_REV` `d2c16c5` (`.lake/go-src/raft`), etcd's server at the fork's `8c28a42`
(`.lake/go-src/etcd`; the line numbers the d6 note cites from the server project's pin differ by a
few lines, e.g. its `server.go:2078` is `2064` here).

## The problem, restated

After a power loss etcd restarts raft with `RestartNode` and a `MemoryStorage` whose snapshot's
`ConfState` is replaced by the backend's members (`bootstrap.go:105-116`,
`buildConfStateFromV3store`): the configuration at the backend's consistent index `|A₀|`. The WAL
can end below that point (`σ.last < |A₀|`), and its commit too (`σ.commit < |A₀|`), because the
server applies a `Ready`'s committed entries before it saves the `Ready`'s hard state and entries
(`raft.go:240` `applyc <- ap`, then `:264` `storage.Save`). `RestartNode.spec` requires
`a ≤ σ.commit`. Lowering the point to `a' = min |A₀| σ.commit` fails at the next conf entry
`k > |A₀|`: etcd never passes the replayed conf entries of `(a', |A₀|]` to raft
(`server.go:2063-2065`: `ApplyConfChange` only when `shouldApplyV3`, false at or below the
consistent index; `ValidateConfigurationChange` returns `nil` for them, `cluster.go:307-309`, so the
no-op `ApplyConfChange` of a refused change is not called either), so `node.ApplyConfChange.spec`'s
`skippedIn γ l a' k` is false: those entries were decided `.apply`.

A second instance, not named in step 3 but in round 4's item 1: a kept snapshot (`MsgSnap` at index
`k ≤ ci`, `applySnapshot.specKeep`) installed during the replay window. `node.Advance.spec`'s
snapshot arm puts the view at `⟨k, m⟩`, `k < |A₀|`, and the conf entries of `(k, |A₀|]` come back and
are skipped by etcd the same way: the next `Advance` needs `skippedIn γ delivered k _`, false for the
same reason. Any fix must cover both.

## 1. What the Go code does, and whether raft stays correct

**State after `RestartNode`.** `newRaft` (`raft.go:439-489`) reads `InitialState`
(`storage.go:129-133`: the snapshot's `ConfState`, i.e. the backend's) and restores the tracker from it
(`confchange.Restore` with `LastIndex = σ.last`, `raft.go:472-479`); nothing about the configuration
depends on an index. `loadState` (`:2038-2045`) sets `committed = σ.commit`, `Term`, `Vote`;
`Applied` is 0 in etcd (`raftConfig`, `bootstrap.go:580-592`), so `applied` is the snapshot's index
`σ.b`. The node is a follower at the stored term with configuration `C(|A₀|)`, log up to `σ.last`,
commit `σ.commit`. No assertion checks the configuration against the log; nothing panics.

**Delivery and apply.** Raft hands out `(σ.b, σ.commit]`, later more as its commit grows; the server
skips the conf entries `≤ |A₀|` (above). Raft's commit index moves only by a leader's `MsgApp`
(after log matching, `maybeAppend`, `log.go:109`) or heartbeat (`handleHeartbeat`, `raft.go:1850`, a
commit the leader bounds by the follower's match), so an entry of `(σ.commit, σ.last]` that a later
leader overwrote (the stale case of round 4's step 1) is never handed out as committed: it is replaced
first. (And the server would skip it anyway, being `≤ |A₀|`.)

**Campaign.** `hup` (`raft.go:991-1009`) requires `promotable` (`:1947-1950`: the node is a voter of
its tracker, `C(|A₀|)`, with no snapshot pending) and no conf entry in `(applied, committed]`
(`hasUnappliedConfChanges`, `:1013-1039`). The conf entries of `(σ.b, σ.commit]` are already reflected
in `C(|A₀|)`, so this check is only conservative: the node waits until etcd has advanced past them
(liveness, not safety). A node removed by a conf entry of `(σ.commit, |A₀|]` is not in `C(|A₀|)`'s
tracker and never campaigns.

**Can it win without the committed log?** Its log is a log raft really had (the WAL's state), and its
configuration is a committed one, `C(|A₀|)`; only the pairing is new: the configuration's last conf
entry `p ≤ |A₀|` may be past the log. Let `p` be committed by a commit fact at term `t_w` whose quorum
`Q` is of the configuration just before `p` (raft proposes a conf entry only with every earlier one
applied, and at most one is unapplied at a leader: I3), hence adjacent to `C(|A₀|)`: `Q` meets every
quorum `V` of `C(|A₀|)` at some voter `v`.

- If the campaign term `T > t_w`: `v`'s log holds an entry of term `≥ t_w` at an index `≥ p`
  (committing needs an entry of the leader's term, acknowledged), and the candidate's last term is
  below that unless its log holds `p` (an entry of a higher term below `p` would contradict log
  matching and leader completeness at `t_w`), so `v` refuses; this is the ordinary adjacent case.
- If `T ≤ t_w`: the commit happened before the restart (`p ≤ |A₀|` was applied), so `v` had durably
  acknowledged at term `≥ t_w` before the candidate asked (a follower's `MsgAppResp` is sent after its
  `Save`, `raft.go:264` before the follower's send at `:329`); `v` refuses a vote at `T < t_w`, and at `T = t_w`
  it knows that term's leader (`canVote` needs `lead == None` or a vote for the candidate already),
  who is not this node (its stored term would then be `≥ T`: a candidate persists its term before its
  vote requests leave).

So the node cannot win before it holds the committed log through `p`; after that its configuration is
the fold of its own log, and the usual argument applies. A node that does catch up as a follower and
then wins (its commit may still be `< |A₀|`: a new leader commits only once an entry of its term is
acknowledged) leads with `pendingConfIndex = lastIndex` (`becomeLeader`, `:976`), so it proposes no
conf change until it has applied past everything it holds.

**Verdict: no misbehaviour found.** Raft stays correct in this state; the only effect is the
conservative campaign refusal above. Nothing to file in `issues/` or `nonissues/` (the related
snapshot case is `nonissues/etcd-replay-snapshot-confstate-ahead.md`, already filed).

## 2. Candidate restatements

The relevant internals: `RInv` (`Protocol/StepRInv.lean:264`) has `applied_cidx : applied ≤ cidx`,
`cidx_commit : cidx ≤ commit` and `cfg : cfgFold dec c0 (full.take cidx) = some cfg` (the
configuration is a fold of the node's own log); `dynEnv` (`Protocol/GhostState.lean:159`) hands the
step rules that configuration as `CfgAt` of the own full log's prefix at `a ≤ commit` (`a = commit` at a
candidate); a winner's record `isWinCore` (`Protocol/Ghost.lean:1048`) has its configuration as
`CfgAt` of its campaign log's committed prefix `F0.take k`, and `lc_core`'s far cases
(`Protocol/LeaderCompleteness.lean:456` `lc_far_newer`, `:516` `lc_far_older`) count conf entries of
that prefix. The node API ties the client's view index to raft's `capplied` (= `RGh.cidx`) in
`runCfg` (`InvNodeChan.lean:1039`: `ca ≤ capplied`, the entries between skipped, `undecFree`), and
`StepR.advance`/`applyConf` (`Protocol/StepR.lean:418`, `:440`) take `NoUndecConfIn` (every conf
entry the configuration index passes decided skip), used only through `cfgFold_noUndec`
(`StepRInv.lean:186`) in `RInv_advance`/`RInv_applyConf` (`:862`, `:907`).

### A. `RestartNode` at any committed point (`a ≤ |l|`, the spec plan's form)

`SpecPlan/Spec/go_etcd_io/raft/v3/RestartNode.lean` (round 1) already drops `a ≤ σ.hs.commit`, and its
`node.Advance.spec` lets the client name the view after a snapshot at any committed `a ≥ s.index`
whose configuration the snapshot lists (covers the kept-snapshot case). The obligation it leaves to
raft's proof is `notes/specs-only/req/go_etcd_io_raft_v3.md`, item 8, with the argument of section 1
("unchecked whether it closes"; R1 reverts to `a ≤ commit` as a filed scope restriction if not).

Invariant changes:
- `RGh` gains the committed prefix the configuration is a fold of (`cpre`, `|cpre| = cidx`);
  `RInv.cfg` becomes `cfgFold dec c0 cpre = some cfg` with `cpre` and `full.take commit` prefix-related,
  `cidx_commit` goes (or becomes `cidx ≤ commit ∨ the node holds no entry it would apply past it`);
  `ownRaftGhostR` (`RefinementDyn.lean:186`) adds `isCommitted γ cpre` and the conf-position witnesses
  of `cpre` (`W`, which today stop at the node's commit).
- `dynEnv`: the configuration is `CfgAt` of a committed `L` (not the own log); the candidate's `a = commit`
  and the leader's `confCount (drop a) ≤ 1` restated over `L`.
- `isCampK`/`isWinCore`: the winner's configuration `CfgAt γ M L c` for a committed `L` with
  `F0.take k ≼ L` or `L ≼ F0.take k`.
- `lc_core`: `lc_far_newer` gets the case `k_c < n < |L|` (the candidate's log may not reach `n`):
  use the witness of `L`'s last conf position (adjacent to `C(L)`); when its term is `< T`, `lc_adj`
  puts it into `F0`; when `≥ T`, a new lemma refutes the vote (the overlapping voter's durable term is
  at least the witness's: needs a persistent per-voter term lower bound from acknowledgements, or the
  vote table extended to acks of terms `≥ T`). `lc_far_older` and `win_fresh` re-checked with `L`'s
  conf count in place of `F0.take k`'s.
- `RestartNode.lean` (`RInv` at `a`, lines 795-810), the snapshot path (`applySnap` with a view ahead),
  the node API's `runCfg`.

Proofs touched (grep and `etc/importers.py --uses`): `Protocol/StepRInv.lean` (1183 lines),
`StepR.lean` (593), `RefinementDyn.lean` (882), `GhostState.lean` (3456; `dynEnv`), `Ghost.lean` (3764;
`isCampK`, `isWinCore`), `StepGhost.lean` (1723), `Refinement.lean` (5806: `dynEnv` at the win,
campaign, commit, read rules, lines 909-5300), `LeaderCompleteness.lean` (1438), `TracedWinGhost.lean`
(315), `InvRawnode.lean` (3858), `StepGhostMode.lean` (1568), `InvNodeRun.lean` (2871),
`TracedNodeRun.lean` (1259), `TracedRawNodeAdvance.lean` (2636), `InvNodeChan.lean` (1771),
`RestartNode.lean` (1199), the `Advance` specs and proofs; callers of `RestartNode.spec`: kv
(`StartCluster`, `Results`), kvreconf (`Config`, `Cluster__startNew`, `StartCluster`), kvdurable
(`Config`, `Cluster__start`), the server (`InvNodeStart`, `bootstrappedRaft__newRaftNode`,
`NodeApiLink`); plus the generated copies (`RaftTla/`, `RaftNoAx/`). Size: the protocol part is new
leader-completeness reasoning, several thousand lines of affected proof and several sessions; the
term case is the risky step.

Axioms or premises: none if the argument closes. If it does not, the fallback is the current
`a ≤ commit`, which is the blocker.

### C. `RestartNode` at `a ≤ |l|` with the membership constant over `[min a σ.commit, a]`

Premise `□ ∀ j ∈ [min a σ.commit, a], confAt γ j m`; internally raft starts at `cidx = min a σ.commit`
(so `RInv` is unchanged) while the client's view is at `a`; `runCfg` gains a window clause
(`capplied ≤ ca`, the persistent window fact), and `Advance`/`ApplyConfChange` move `cidx` across the
window by the fold equality the window fact gives. The server meets the premise (`srv_confAt_simple`,
`NodeBridge`/`InvApplyAll`: every committed prefix's membership is `Membership.simple cfg`); the other
callers take `[a, a]`. It fixes the restart, but not the kept snapshot in the window: the snapshot
arm's post puts the view at `k < |A₀|` again, and fixing that needs a conditional snapshot post (view
stays at `ca` when `k` is in the recorded window). Same raft-internal work as D, plus the window
bookkeeping, plus a special case in the API. Not recommended.

### D. Keep `RestartNode`; the consumers take the configuration, not the skips (recommended)

What raft needs when its configuration index moves from `ca` to `b` (an `Advance` past conf entries, an
`ApplyConfChange` at `k`) is only that its configuration is the committed one at `b`: `RInv.cfg` at
`b`, which `cfgFold_noUndec` derives today from the skips. State that directly:

- `node.ApplyConfChange.spec`: `skippedIn γ l v.applied k` becomes `confAt γ k v.membership` (the
  configuration just before entry `k` is the view's).
- `node.Advance.spec` (no-snapshot arm): `skippedIn γ st.delivered v.applied st.delivered.length`
  becomes `confAt γ (max v.applied st.delivered.length) v.membership`, and the post's view moves to
  `⟨max v.applied st.delivered.length, v.membership⟩`. The move is needed: with the view left below the
  delivered log, a client could then `ApplyConfChange` an entry raft's `applied` already passed, taking
  raft's configuration back below its applied index (the case of
  `issues/raft-advance-before-applyconfchange.md`; internally `applied ≤ cidx` breaks).
- The traced variant (`Proof/.../TracedAdvanceSpec.lean`) the same.

The new premises are weaker: `confAt_skipped` (`InvNodeRule.lean:624`) with `nodeConfig_confAt`
(`:104`) and `deliveredLogLb_committed` (`InvNode.lean:1532`) derives them from the old ones, so a client
that skips changes by one lemma application per call. `RestartNode.spec` is unchanged; the server
restarts at `a' = min |A₀| σ.commit` (round 4's item 4), with `confAt γ a' m` from `srv_confAt_simple`,
skips the replayed conf entries, and meets both new premises at every index from `srv_confAt_simple`,
in the restart window and after a kept snapshot alike.

Raft internals:
- a pure lemma `RInv_cidxJump` (`StepRInv.lean`): `cidx ≤ b ≤ commit` and `cfgFold dec c0 (full.take b)
  = some cfg` give `RInv` at `cidx := b` (`applied_cidx` and `i3`/`cand` are unaffected: `i3`'s
  at-most-one is over `applied`, and `dynEnv`'s leader clause only improves with a larger index); and its
  ghost form on `ownRaftGhostR`/`ownStepGhost` (`cidx` is ghost-only). `StepR.advance`/`applyConf` keep
  their hypotheses, applied after a jump over an empty range; or, equivalently, their `NoUndecConfIn`
  hypothesis is replaced by the fold fact (`RInv_advance`/`RInv_applyConf` use nothing else);
- `undecFree` (`InvRawnode.lean:2126`) becomes the fold fact over recorded decisions
  (`∃ M, decLb γ M ∗ ⌜cfgFold (effDec dec M) c0 (D.take b) = some cfg⌝`), which the ghost absorbs as
  today (`ownStepGhost_absorbM`, monotone in `M`); `RawNode.Advance`'s spec premise and `DynCCPreOp`
  (`ApiVocab.lean:378`) in that form;
- `runCfg` (`InvNodeChan.lean:1039`): with both moves applied to the view and to `capplied`, `ca =
  capplied` at the rendezvous points, and the `undecFree ca capplied` clause goes (a simplification);
- the code proofs: `node__Advance.lean` (35), `NodeAdvanceTraced.lean` (500), `InvAdvance.lean` (425),
  `TracedRawNodeAdvance.lean` (2636, the A1 block near 2245-2265), `node__ApplyConfChange.lean` (485),
  `InvNodeRun.lean` (2871, the `confc` arm near 1475-1490 and `DynCCPreOp` near 2500),
  `TracedNodeRun.lean` (1259, near 824), `node__run_gated.lean` (1341, `runCfg`), `StepGhostMode.lean`
  (1568, `GMode.Pre`'s A1), `StepLemmasR.lean` (877, `DynHyp`'s A1), `RestartNode.lean`/
  `TracedStartNode.lean` (`runCfg` at the start, one use each). The protocol's leader completeness,
  `dynEnv`, the winners table and `Refinement.lean` are untouched.

Clients (`etc/importers.py --uses node.Advance.spec`/`node.ApplyConfChange.spec`/`skippedIn`): kv
(`Defs`, `KV__run`, `KvRunSnap`, `Reconf`), kvreconf (`ApplyConfLemmas`, `ConfLemmas`, `ConfStep`,
`Defs`, `EntryLemmas`, `RunApply`, `RunInv`, `RunSnap`, `Replica__applyConf`, `Replica__run`),
kvdurable (`ApplyLemmas`, `Defs`, `Replica__run`, `RunInv`, `RunLemmas`, `Replica__applyConf`, the spec
`Replica__applyEntry`), the server (`InvCfgView`, `NodeBridge`, `NodeStartLaws`, `NodeStartLinked`,
`NewServer`, `NewServerR`), raft's `TracedNodeApi`/`TracedLinked`/`Link`/`Linked`; and the copies in
`RaftTla/` (`etc/gen-raft-tla.py`) and `RaftNoAx/` (`etc/copy-part.py`). Each client: `confAt_skipped`
where it passed `skippedIn`, and its view invariant re-established at the moved index after `Advance`
(a client that applies every conf entry before `Advance`, as the server and kvreconf do, holds the view
at its last applied conf entry `≤ |delivered|` with no conf entry after it, so the larger index
satisfies the same invariant). The server's `srvCfgOk` (`InvCfgView.lean:150`) and `srvCCPre` (`:141`)
drop their `NoConfChangeIn` conjuncts (they existed to produce `skippedIn_noConf`): the replay window
breaks them, and `srv_confAt_simple` replaces them.

Size: about 15 raft files edited locally (the A1 plumbing; estimate 400-800 changed lines, no new
protocol reasoning), the two specs and their interfaces, one-line changes at some 25 client call sites
plus the view-index adjustments, and the server's step 3 itself (`NodeStart` 938, `InvNodeStart` 365,
`bootstrappedRaft__newRaftNode`, `rnBootPre`/`NodeStartSpecR`, `InvCfgView` 544, `NodeBridge` 725).
One to two sessions for raft and the examples; the server part is d6's step 3.

Limit: D relies on the server's configuration being the same at `a'` and `|A₀|`
(`srv_confAt_simple`, D3: the server's membership is static). With real membership changes in
`(σ.commit, |A₀|]`, `confAt γ a' m` with the backend's `m` is false, and only A covers the restart.
D's premises stay valid under A (they are weaker than the skips), so A can come later without undoing D.

### Rejected

- **B. A client-side law moving the view** (`nodeConfig ⟨a, m⟩ ∗ confAt γ b m ==∗ nodeConfig ⟨b, m⟩`):
  the configuration index is the run loop's ghost state (`runCfg`, `ownStepGhost`), not the client's,
  and `b > commit` would break `RInv`; it is D with the move done outside raft's steps.
- **Lowering the point with today's API** (round 4's item 4): the step-3 finding (`skippedIn` false).

## 3. Axioms and premises

None of A, C or D needs an axiom or a new top-level premise. D's new premises are met by facts the
clients already have (`confAt_skipped` from their skips; the server's `srv_confAt_simple`, proved).
A needs new protocol reasoning (the term case of section 1), not an assumption; if it cannot be
proved, A is not available (the fallback is today's `a ≤ commit`), and an axiom stating it would not be
acceptable.

## 4. Recommendation and plan

**D now; A stays raft's open obligation** (the spec plan's item 8). D fixes both instances (the
restart and the kept snapshot in the window), is local to the node API's A1 plumbing, makes raft's
premise the semantic one (its configuration equals the committed configuration where its index lands)
and simplifies `runCfg` and the server's view invariant. It does not converge on the spec plan's
`RestartNode` (which takes A); the ledger entry should say so and why (A's argument is unchecked and
large; the etcd proof's membership is static).

Steps:
1. Ledger (`notes/specs-only/ledger.md`): `node.ApplyConfChange.spec` and `node.Advance.spec`, the defect
   (etcd skips replayed conf changes decided `.apply`: `skippedIn` false after a restart at
   `min |A₀| σ.commit` and after a kept snapshot), the proposed premises and the moved view, before the
   specs change. Check the spec plan's `node.ApplyConfChange`/`node.Advance` (`confSkipped`) for the same
   change.
2. Pure: `RInv_cidxJump` (or the fold-fact hypotheses of `StepR.advance`/`applyConf`); its ghost form.
3. `undecFree` to the fold fact; `RawNode.Advance`'s premise, `DynCCPreOp`, `GMode.Pre`, `DynHyp`.
4. `runCfg` (`ca = capplied`), its maintenance lemmas, the start proofs.
5. The two specs and their proofs (untraced and traced); check that the traced path (`RaftTla/`, where
   `ApplyConfChange` already requires `m' = v.membership`) needs nothing more; regenerate
   `interface/` (`etc/gen-interface.py etc/api/raft.txt`), `RaftTla/` and `RaftNoAx/` copies.
6. Clients kv, kvreconf, kvdurable: `confAt_skipped` at the calls, the view after `Advance`.
7. Server (d6 step 3): `srvCfgOk`/`srvCCPre` without `NoConfChangeIn`, `confAt` from
   `srv_confAt_simple` at `NodeBridge`'s calls, the restart at `a'` (`NodeStart`, `InvNodeStart`,
   `bootstrappedRaft__newRaftNode`), `rnBootPre`'s and `NodeStartSpecR`'s `|A₀| ≤ σ.commit` dropped
   (round 4's item 4), `σ.b ≤ a'` from the backend's `σ.b ≤ i`.
8. `etc/tcb-report.py --check`: no axiom or `sorry` change expected.

A, when the server's membership changes are verified: the plan of section 2.A, starting with the term
case of `lc_far_newer` (a pen-and-paper check of item 8's argument against the ghost state's facts:
whether acknowledgements give a per-voter durable term lower bound the vote table can read).

## Implementation of D (2026-11-24, branch `raft-restart-confpoint/2026-11-24`)

Checkpoint log (newest last). Ledger entry: `notes/specs-only/ledger.md`, 2026-11-24 (committed first).

**Raft internals (as built).**
- `CfgKeep dec l lo hi cs` (`Protocol/StepR.lean`): folding the entries of `[lo, hi)` from `cs` gives `cs`
  back; replaces `NoUndecConfIn` in `StepR.advance`/`applyConf` (lemmas `of_le`, `fold`, `of_folds`,
  `congr`, `prefix`, `of_prefix`, `trans`, `mono_dec` in `StepRInv.lean`/`StepR.lean`). `RInv_cidxJump`
  (`StepRInv.lean`) and its ghost form `ownStepGhost_cidxJump` (`InvRawnode.lean`).
- `undecFree` replaced by `cfgKeepIn γ md D lo hi cfg` (`InvRawnode.lean`); `DynCCPreOp` (`ApiVocab.lean`,
  and RaftNoAx's own copy) takes `CfgKeep dec D ca k cfg`; `DynHyp`/`GMode.Pre` take `CfgKeep`.
- `RawNode.Advance.spec`'s `HA1`: `cfgKeepIn γ rs.mode rs.delivered rs.capplied rs.delivered.length rs.cfg`.
  `TracedRawNodeAdvance`: before stepping the queue the ghost index jumps to `max capplied |delivered|`
  (every acknowledgement of the queue is at most `applying`, so each step passes no entry; the queue
  may hold several `MsgStorageApplyResp`s, and `CfgKeep` is not monotone in its range).
- `runCfg`: the driver's view at or ahead of `capplied` (`capplied ≤ ca`, ahead only within `rsDlv`,
  with `cfgKeepIn (rsDlv rs) capplied ca rs.cfg`); the `advancec` rendezvous moves the view
  (dynamic mode, no snapshot) to `max ca |delivered|` (`capPay`/`capAns`/`loanReq`/`loanCfg` take the
  length `n`, `advanceP γ L x n`); `advRet0` carries `|delivered| ≤ ca_d`; `runCfg_a1`/`runCfgR_a1`/
  `runCfg_advance` rebuilt; `dynCCPreOp_transfer` from the view ahead.
- API wrappers: `confAt_keep_impl` (`InvApiDec.lean`) turns two `confAtU`s of one membership into a
  `CfgKeep` over the delivered log; `node.ApplyConfChange`'s and `node.Advance`'s wrappers use it.

**The specs (as stated).** `node.ApplyConfChange.spec`: `confAt γ k v.membership` in place of
`skippedIn γ l v.applied k`. `node.Advance.spec` (and `node.Advance.tracedSpec`), no-snapshot arm:
premise `confAt γ (max v.applied st.delivered.length) v.membership`, post
`nodeConfig n γ N ⟨max v.applied st.delivered.length, v.membership⟩`.

**Clients.** kv (`KV__run`), kvreconf (`appNode_open` returns the `confAt` and takes the view back at
`k`; `wp_conf_apply` by `confAt_skipped`), kvdurable (same; the restart-window arm keeps the view ahead),
kvnet (KvNet's own copies of kvdurable's three files), tracecheck (`Cluster__app`, `Cluster__handleReady`,
`ProbeALinked`), the server's `NodeBridge` (minimal: `confAt` from its `NoConfChangeIn` facts, the view
moved after `Advance`). RaftTla/RaftNoAx/KvNet copies regenerated.

**Checkpoint 2 (built).** VM build green for raft `Results`/`Linked`/`TracedLinked`, kv, kvreconf,
kvdurable (`Results`, `TopLevelRobustness`), tracecheck (RaftTla), kvdurablenoax (RaftNoAx), kvnet
(`TopLevelRobustness`, KvNet); the server's `Link` and its restart leaves green (subagent build).
Server (d6 step 3, as built): `srvCfgOk`/`srvCCPre` without `NoConfChangeIn`; `NodeBridge` gets `confAt`
from `srv_confAt_simple` (`raftApplyCC_of_isNode` takes `srvRaftLogInv`); `raftNode_of_RestartNode`
restarts raft at `a' = min |A₀| σ.commit` with the view at `⟨a', simple cfg⟩`. **Not dropped:**
`NodeStartSpecR`'s `|A₀| ≤ σ.commit`, still used by `replaySeed_facts` (d6 round 4 item 3) and
`rnRestartOk`'s restart disjunct (item 2, behind the blocked step 1); it no longer feeds `RestartNode`.
**Next:** interface regeneration (`etc/gen-interface.py etc/api/raft.txt`), `etc/tcb-report.py --check`,
then the remaining `NodeStartSpecR` bound once items 2-3 land.
