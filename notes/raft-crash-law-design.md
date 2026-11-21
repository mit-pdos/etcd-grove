# Raft's crash law: design study (2026-11-21)

Decision A of `notes/kvnet-proof-plan.md`: a replica process killed at any instruction must leave
its id restartable, i.e. the crash obligation of `goose_dist_crash_adequacy` (`Hwp`'s wand, given
the dead generation's `crashed`) must produce `nodeVacant γ id` again. Read-only study: nothing
built, no proof changed. Line numbers are at `f7d9ff4459`.

## (a) What a running node holds that `nodeVacant` needs

`nodeVacant γ id` = `nodeVacantU` = `raftIdSlot γ.raft id` (`InvNode.lean:665`,
`InvApi.lean:1803`, `Protocol/GhostState.lean:2818`). Its conjuncts, and where each is during a run:

| piece of `raftIdSlot` | kind | held while running by |
|---|---|---|
| `ghostVar γs.1 ½ V` (virtual maps) | exclusive, timeless | `ownRaftGhost`'s `Hvirt` (`GhostState.lean:2888`) |
| `slotLive γ id 1 g` (generation, `ghostVar γs.2.2 ½ g`, `:2788`) | exclusive, timeless | split: client `nodeLiveRaw ½` (`InvNodeChan.lean:1258`), `run` (`stopAns`, `:1308`) |
| `slotFree γ id g` (`g ↪[γs.2.1] none`, `:2792`) | exclusive | node, or replaced by the client's `pendBatch` between cut and enter |
| `ghostMapAuth γm 1 terms` + frags | exclusive + persistent | `ownLogGhost`'s `Hterms` (`:2838`) |
| `ghostMapAuth γw 1 wins` + frags | exclusive + persistent | `ownLogGhost`'s `Hwins` |
| `ghostMapAuth γl 1 lcm` + frags | exclusive + persistent | `lcmOwn` (`:1337`) |
| `ghostMapAuth γq 1 rqm` + frags | exclusive + persistent | `rdOwn` (`:1635`) |
| `slotInv`, `raftCommitInv`, `rdCredInv`, `id ≠ 0` | persistent | everywhere |

The key observation: **`raft_stop` (`Protocol/Enter.lean:1866`) is already a crash law in all but
ownership.** It takes only `slotLive 1 g ∗ ownRaftGhost γ id s md` for *any* `s`, uses nothing
physical, discards everything but the six exclusive pieces above (outbox facts, read credits,
proposal tickets, `lcmLead`'s `monoNatAuthOwn γc`, `rdLead`'s registry, `leadLogOwn`'s term log), and
bumps the generation, so a batch cut in `g` and not entered is dead (its `pendBatch` names `g`,
the slot's current queue entry is `g+1 ↦ none`). So the whole problem is: keep those six timeless
pieces somewhere a crash does not destroy, while the run loop keeps updating them.

When are they touched? Only at five kinds of points:
- the **win** (candidate → leader): the four inserts `Refinement.lean:923` (wins), `:1016` (terms),
  `lcmOwn_win` `GhostState.lean:1409`, `rdOwn_win` `:1734` (called at `Refinement.lean:1407,1410`);
  traced builds also insert in `TracedWinGhost.lean:182`, `TracedRaftStepRecvVoteRespWonFx.lean`,
  `TraceSimLeader.lean`;
- the **cut** (`ownRaftGhost_cut`, `Enter.lean:446`, used once: `InvRawnodeReady.lean:2578`): `V`;
- **enter** (`raft_enter`, `Enter.lean:831`; API `readyEnter`, `InvNode.lean:949`; the wand in
  `Spec/.../RawNode__Ready.lean:110-118`): `slotLive q g` read;
- **restart**/**start** (`raft_restart` `Enter.lean:1295`, `raft_start_boot` `:1612`) and **stop**.

Every other use of `ownRaftGhost` (95 files; ~300 fact extractions such as `ownStepGhost_nsLink`)
only passes these conjuncts through or reads pure facts about their contents (`TermsOk`, `LcmOk`,
`lcm !! s.term = some γc`).

A fact that constrains both routes: the only thing that tells a thread its generation is alive is
`notCrashed` (state interpretation). Any design in which a crash rule may change state that a live
thread later updates needs that thread to refute the "already crashed" case, i.e. to hold
`notCrashed` at the update (`wp_notCrashed_acc`/`wp_atomic_nc`, `GooseLang/Ext/Fs/NotCrashedAcc.lean`).
Checked against both routes below: neither avoids it at cut and enter.

## (b1) Route 1: a per-generation crash invariant (recommended)

Ghost state (new, in `GhostState.lean` beside `raftIdSlot`), at the ambient generation's crash name:

```lean
structure CrashX where (V : DurMaps) (g : Nat) (terms : GMap w64 TermRec)
  (wins : GMap w64 (GSet w64)) (lcm rqm : GMap w64 GName)
-- the six timeless pieces at contents X, with the leader-side fragments (timeless)
def slotX (γ : RaftNames) (id : w64) (X : CrashX) : IProp GF
def nodeCrashInv (γ : RaftNames) (id : w64) (γx γt : GName) : IProp GF :=
  inv (raftN γ .@ "crash" .@ id)
    ((∃ X, ghostVar γx ½ X ∗ slotX γ id X) ∨ (crashed ∗ dghostVar γt (.own 1) ()))
```

`ownRaftGhost`/`ownLogGhost`/`lcmOwn`/`rdOwn` keep their signatures; their five exclusive
conjuncts become `∃ γx γt, nodeCrashInv γ id γx γt ∗ ghostVar γx ½ X` with `X`'s fields standing
where the authorities' contents stood (all pure facts unchanged). `slotLive` leaves `nodeLiveRaw` and
`stopAns`: the generation is constant during a run, so the client and `run` keep only a persistent
`nodeGen γ id g γx` (the invariant holds `slotLive 1 g`).

Raft-internal laws (all `notCrashed -∗ … ={E}=∗ notCrashed ∗ …`, best written with an
`ncfupd` modality as in Rocq Perennial: `|NC={E}=> P := notCrashed -∗ |={E}=> notCrashed ∗ P`, with
`wp_ncfupd` = `wp_notCrashed_acc`; a general Perennial change, for `notes/perennial-changes.md`):
- the win's four inserts open `nodeCrashInv` (mask `⊤ \ raftRegN` minus the crash namespace;
  it is under `raftN` but disjoint from `slotN`, `raftLogN`, `raftRegN`);
- `ownRaftGhost_cut`, `raft_enter`, `raft_restart`, `raft_start_boot` open it around their existing
  `slotInv` opening;
- `raft_crash : slotX γ id X ∗ slotInv γ id ∗ raftCommitInv γ ∗ rdCredInv γ ={E}=∗ raftIdSlot γ id`
  (`raft_stop`'s proof minus the destructuring of `ownRaftGhost`); `raft_stop` becomes
  "split `ownRaftGhost`, then `raft_crash`".

API (`InvNode.lean`, sealed like `nodeVacant`):

```lean
nodeVacantA γ id γx : IProp   -- armed vacancy: view at X with a free queue + slotFree + crash inv
nodeCrashTok γ id γx : IProp  -- dghostVar γt 1 + crash inv + raftIdSlot's persistent part
theorem nodeVacant_arm : nodeVacant γ id ={E}=∗ ∃ γx, nodeVacantA γ id γx ∗ nodeCrashTok γ id γx
theorem nodeCrash : crashed -∗ nodeCrashTok γ id γx ={E}=∗ nodeVacant γ id   -- ↑(raftN) ⊆ E
```
- `StartNode.spec`, `RestartNode.spec`: `nodeVacant γ cv.ID'` → `nodeVacantA γ cv.ID' γx` (their
  inner `raft_*` steps already fire at a step: the AU at the `InitialState` read, `wp_atomic_nc`).
- `node.Stop.spec`: post `nodeVacantA γ id γx` (same generation, same `γx`), so a cooperative
  stop-then-restart (kvdurable) stays covered and needs no crash.
- `readyEnter` and `RawNode.Ready`'s enter wand: `|NC={E}=>` in place of `|={E}=>`.
- The client's handle keeps `nodeRunning n γ N q` (`live` share + `nodeGen` + inv), and the boot
  proof's frame keeps `nodeCrashTok`: kvnet's boot obligation turns `P i L`'s `nodeVacant` into
  `nodeVacantA` (to the WP) and `nodeCrashTok` (into `Hwp`'s crash wand, built before the WP runs:
  `DistAdequacy.lean:754-763`), so a crash before `RestartNode` is covered too.

Soundness (why raft's invariants survive each crash point; the crash wand runs `nodeCrash`, which
refutes the right disjunct by `γt`'s exclusivity, takes `slotX X`, closes with `crashed ∗ tok`,
then `raft_crash`):
- **Atomicity.** Every change to `X` happens inside one fancy update holding the invariant open, so
  a crash (between steps) sees a consistent `X`: no "mid-update leader map".
- **Pending batch.** As in `raft_stop`: the generation moves to `g+1` with `g+1 ↦ none`; the stale
  `pendBatch g` can never enter (enter needs the slot's current generation; the dead client could
  not anyway). Its promises were never minted, so `votesTbl`, `winTbl`, `committedJust`, Leader
  Completeness are unaffected; the messages behind them (`outMsgOk`'s wands over the batch's
  fragments) are sent only after enter, so none is in flight. Leader messages sent before enter
  (`readyLeaderMsgs`) carry no pending promise.
- **Leader-side maps.** Preserved whole, with their fragments, under the same names: every
  persistent fragment (in messages, `isWin`, `isTermLog`, `cmtLb`, `rqLb`) keeps its meaning.
  `raft_restart` already rebuilds a follower's `TermsOk`/`WinsOk`/`LcmOk` from `campKey`
  (entered campaigns are at most the durable term): a restarted node never re-leads a term it led.
- **Volatile state.** Dropped exactly as at a stop (review 1's N6): outbox, tally, read credits,
  proposal tickets, `lcmLead`/`rdLead`/`leadLogOwn` authorities of the led term (that term is over
  for this id, by the previous point). Lost read-index and proposal waiters are liveness only.
- **In-flight messages.** `sentMsg`/`isMessage` are persistent and name only global ghost state;
  the restarted node's `raft_restart` does not depend on them.
- **Durable state.** `raftState γ id S` (`ownDurGhost`, the other half of the promise authorities)
  is the store's, in its durable-file invariant (plan C: *enter* at `durWriteSync`).

## (b2) Route 2: fresh names per incarnation

Per-(id, generation) names for the four leader-side maps, registered persistently
(`genNames γ id g ↦□ (γm, γw, γl, γq)`), plus a retire rule
`crashed_L ∗ genOwner γ id g L ={E}=∗ raftIdSlot' γ id (g+1)` minting empty maps (a restarted
follower's `TermsOk` holds trivially). The node owns its generation's authorities outright, so the
win needs no `notCrashed`.

What it costs:
- **Fragments across generations.** `RaftNames.reTerms/reWins/reLcm/reRdq` (`Protocol/Ghost.lean:240-288`)
  become the registry; the four wrappers that name them, `isTermLog` (`Ghost.lean:1160`, 29 lines in
  6 files), `isWinCore` (`:1049`, 29/5), `cmtLb` (`:1119`, 16/3), `rqLb` (`GhostState.lean:121`,
  18/3), quantify over the generation. Their agreement (`isTermLog_agree` `Ghost.lean:1758`, the
  frozen-quorum agreement in `win_fresh` `LeaderCompleteness.lean:1226`, the read index's use of
  `cmtLb`/`rqLb` against the leader's own authority) needs "two fragments of one `(id, t)` are of
  one generation": a new per-id invariant that generation `g`'s keys lie in `(T_g, T_{g+1}]`,
  `T_g` the restart term. Proving `t ≤ T_{g+1}` at retire, without the dead node's authority,
  needs each fragment to carry a lower bound on the durable term (from `campKey`'s entered
  campaign and `termLB`), and `T_g < t` a new `ownLogGhost` conjunct (a candidate's term is past
  its restart term). New protocol reasoning in the Election Safety / Log Matching / read-index
  layer, the part of raft that is hardest to re-check.
- **The slot still needs `notCrashed`.** `V`'s half and `slotLive` are shared with the permanent
  `slotInv` (whose durable half must persist). With per-generation slot names, a "zombie" cut or
  enter finds the slot already retired and can refute it only by `notCrashed`: the same `|NC>` at
  cut, enter and restart as Route 1. (A zombie-tolerant slot does not work: a stale batch entering
  after a retire would mint promises against another generation's entered maps.)

So Route 2 saves only the win's plumbing, and pays with a cross-generation disjointness argument.

## (b3) A variant worth keeping in mind: per-term leader maps in the winners' table

At most one node wins a term (`winTbl`, `GhostState.lean:1222`, global, its insert
`LeaderCompleteness.lean:1368`). The four per-id maps are all keyed by terms this id won and are
inserted at that same win; keyed by term alone and kept in `winTbl`'s invariant, they would get
freshness from the table's (`win_fresh`) and leave `raftIdSlot` altogether, so the crash invariant
would hold only `V` and `slotLive` and the win would need no `notCrashed`. `TermsOk`/`WinsOk`/`LcmOk`
(28/10/4 lines) look like freshness only, but `isWinCore`'s per-id frozen quorum is taken *before*
the table entry (`win_fresh` takes `isWinCore`), so the win's order changes. Not checked further;
a later simplification of Route 1 (it changes no API), not a first step.

## (c) Impact estimate (Route 1)

Counts are grep counts over `Proof/` and `Spec/` without the generated parts.

| area | files | estimate |
|---|---|---|
| defs + laws: `ownLogGhost`, `lcmOwn`, `rdOwn`, `ownRaftGhost`, `raftIdSlot`, `slotX`, crash inv, `raft_crash`; lemmas touching `Hterms` (30 lines/7 files), `Hwins` (16/4), `Hvirt` (111/12), the `lcm`/`rqm` authorities (`lcmOwn` 38/4; `rdOwn` 174/47, mostly pass-through) | `Protocol/GhostState.lean`, `Facts.lean`, `ReadIndex.lean`, `StepGhost.lean` | 200-350 lines |
| win path under the invariant, `notCrashed` threaded through `ownRaftGhost_stepC_in`/`stepC` (`Refinement.lean:5397-5610`) and `ownRaftGhostR_stepR` | `Refinement.lean`, `RefinementDyn.lean` | 100-200 |
| `ownRaftGhost_cut`, `raft_enter`, `raft_restart`, `raft_start_boot`, `raft_stop` → NC versions, arm | `Protocol/Enter.lean` (1945) | ~150 |
| NC plumbing beside the existing `£ 1` of each ghost step (≈45 `£ 1` lines in 16 files: `raft__Step/Base` 9, `InvNodeRun` 7, `TracedNodeRun` 7, `StepGhostMode` 4, `TracedRawNodeAdvance` 4, `InvNodeChan` 3, ...); the cut site `InvRawnodeReady.lean:2578` | ~16 | 100-200 |
| the gated `raft.Step` spec: the traced win inserts inside a gate (`TracedWinGhost`), so `StepG`'s gate modality (`LemmasStepGates.lean`) becomes NC, and the hooks' proofs (both trees) supply it | 5-10 | 50-150, **risk** |
| node API: `InvNode.lean`, `InvApi.lean` (`nodeRunning`, `nodeLiveRaw`, `stopAns`), specs `StartNode`/`RestartNode`/`node__Stop`/`RawNode__Ready`, `readyEnter`; proofs `RestartNode.lean:999`, `TracedStartNode.lean:593`, `node__Stop.lean:82`, `node__run_gated.lean:975`; regenerate `interface/` | ~12 | ~200 |
| clients: `nodeVacant` (31 files, 50 lines: kvdurable, kv, kvreconf, `etcdstart`, etcdserver's `NodeStart*`, `InvRestart`, `StopShutdown`, `NewServer*`), `readyEnter` (11 files, 19 lines: kvdurable's `RunDmu`, `Replica__persist`; kv; kvreconf), `RestartNode`/`StartNode` call sites | ~35 | 150-300 |
| copies: `RaftTla/` (`etc/gen-raft-tla.py`), `RaftNoAx/` (`etc/copy-part.py`): regenerated; `RaftTla`'s hand-written hooks and `Init` by hand. `RaftWitness/` has its own raft proof and is untouched. | — | regen |

Total: roughly 1000-1500 changed lines, nearly all mechanical. Clients change only by `imod
nodeVacant_arm` where they get `nodeVacant`, `nodeVacantA` where they store a stopped node's
vacancy, and `wp_notCrashed_acc` where they apply `readyEnter` (kvdurable keeps its `node.Stop`
path and simply drops its `nodeCrashTok`; the etcd server likewise). Route 2 is smaller in the
plumbing rows and adds the slot rows anyway, but replaces "mechanical" with new protocol proofs in
`Ghost.lean`, `LeaderCompleteness.lean`, `ReadIndex.lean` and the win.

## (d) Recommendation

**Route 1**, with an `ncfupd` modality, the crash invariant holding exactly the six timeless pieces
of (a), and the API above (`nodeVacant_arm`, `nodeCrash`, armed `nodeVacantA` in
`StartNode`/`RestartNode`/`Stop`, NC `readyEnter`). It changes ownership only: no ghost name, no
fragment's meaning and no protocol invariant changes, and the crash law is `raft_stop`'s existing
proof. Variant (b3) can later remove the win from the NC points without touching the API.

Main risk: the gated `raft.Step` spec. In the traced instance the win's inserts run inside a caller's
gate, so the gates' modality (`StepG`) must become NC, which reaches the eleven hooks' specs and both
trees' hook proofs (`RaftTla/` hand-written). Check first whether every gate fires before a
non-value expression (needed by `wp_notCrashed_acc`); if one fires at a returned value, move it
before the return. Secondary: masks (the crash namespace must stay outside every mask a step lemma
opens: `raftN γ .@ "crash" .@ id` is disjoint from `slotN`, `raftLogN`, `raftRegN`, but each
`⊤`-masked statement is checked when its lemma changes); and plan B's `nodeTabInv` (`InvApi.lean:1696`):
a new heap can reuse a dead node's location, so `RestartNode`'s table insert must move to a
per-generation table before kvnet's restart proof, independently of this law.

## (e) Gap found when implementation started (2026-11-21)

Checked first, as (d) asks: the traced instance's win. Route 1 as written does not cover it: one of
the six pieces is held **outside any fancy update, across physical steps**, so the invariant cannot
hold it at every crash point.

- `wonGate_rep`'s sibling `wonGate_bl` (`TracedRaftStepRecvVoteRespWon.lean:159-221`) is the
  `"Hgbl"` gate, a `HookGate` update at `⊤` that the caller runs before `traceBecomeLeader`. There
  `ghost_stepWin_reg` (`TracedWinGhost.lean:174`) does the registration and **lends out the term map's
  authority** `ghostMapAuth γm 1 terms` with its return wand. Both go into `trCapB_hookGate` as the
  line's `FxPresUT`/`FxPresU` (`TracedCap.lean:1132`; review round 5's E1: "the new leader's term log
  is created inside the line's step, after its freshness is read").
- That `FxPresU` runs when the trace's atomic update commits (`TraceFire`'s
  `AU <{ ∃∃ L, traceAuth L }> @ ⊤, ∅ <{ traceAuth (L ++ [e]), COMM Q }>`). The commit happens in the
  logger's `TraceEvent` at its linearization point, under the recorder's lock (`isTraceLogger`,
  `RaftTla/.../InvTraceLogger.lean:95`). Inside the line's update, `simFx_becomeLeaderW`
  (`TracedRaftStepRecvVoteRespWonFx.lean:84`) uses the authority twice: to read freshness
  (`becomeLeader_hyps`, `TraceSimLeader.lean:61,94,170`) and to insert the term log.
- So from the gate to the logger's commit, the authority sits in the atomic update's private part.
  That span includes the hook call, `traceNodeEvent`'s allocations of the event and the logger's
  lock. A crash in it finds the left disjunct of `nodeCrashInv` without `terms`. The note's
  "every change to `X` happens inside one fancy update" (soundness, Atomicity) is false here. Making
  `StepG`'s gates NC does not help: the gate is not where the insert happens.

The proof text is shared by both trees (`etc/gen-raft-tla.py`), and the definitions too
(`ownLogGhost`). So the traced win must change even though the traced cluster never crashes. Two
ways out, neither in this note:
1. **An NC trace update.** `TraceFire`'s atomic update and `isTraceLogger`'s contract carry
   `notCrashed` in their atomic pre- and postcondition, so the logger's linearization point supplies
   it (`wp_atomic_nc`). `ghost_stepWin_reg` then lends the view half and `nodeCrashInv` instead of
   the authority, and `FxPresU` opens the invariant itself. This changes the logger contract
   (`RaftTla`'s hand-written `InvTraceLogger`, tracecheck's recorder proof), `TraceFire`'s lemmas
   (`traceFire_nop`/`_mono`/`N`) and `trCapB_hookGate`. The hooks' proofs only pass the update
   through.
2. **Allocate the term log at the gate, before the line.** This redoes E1: `becomeLeader_hyps`'s
   freshness argument would need to work with `terms !! T` already set to the new full log. That is
   new reasoning in the trace simulation.

Nothing was implemented: the user (or the next design round) picks one of these first. Every other
update point the note lists (the untraced win's inserts in `Refinement.lean`, cut, enter,
start/restart/stop) was not contradicted by this check.

## (f) Resolution of (e) (2026-11-21, the coordinating session; open to the user's veto)

Way out 1: the trace's atomic update carries `notCrashed`. The logger's linearization point
(`TraceEvent`'s commit under the recorder's lock) is an atomic step, so `wp_atomic_nc` supplies the
token there; `TraceFire`'s update and `isTraceLogger`'s contract gain it; the win gate hands out
the view half of the term map's authority instead of the authority, and `FxPresU` opens the crash
invariant itself (with the token) to check freshness and insert, as now. Why not way out 2: it
redoes review round 5's E1 (freshness proved with the new term's log already in the map), which is
new protocol reasoning; way out 1 only threads a token through contracts, keeping every argument.
Cost added to (c): the logger contract (`RaftTla`'s `InvTraceLogger`), the tracecheck recorder's
proof, the `TraceFire` lemmas and `trCapB_hookGate`. The untraced cluster's logger is `nil`
(`TraceLoggerOk_nil`): its contract is vacuous, so the main tree's clients are unaffected.
Not yet re-checked: the other update points (the untraced win, the cut, enter, start/restart/stop),
which (e) did not contradict.

## (g) Second gap: the slot's half of the virtual maps is read at ordinary steps (2026-11-21)

Found by the session implementing (f), before any Lean was changed. Section (a) says the six
pieces are touched only at the win, the cut, enter, and start/restart/stop, and that every other
use "only passes these conjuncts through or reads pure facts about their contents". That holds for
the four leader-side authorities: their lookups against foreign fragments, `ReadIndex.lean:435`
(`ownLogGhost_prefix_within`), `GhostState.lean:1991` (`rdOwn_hbResp_pos`) and
`Refinement.lean:4212` (`rdOwn_ack`), are of keys already in the node's own map, so the node's own
persistent fragments (`Htfrags`, `#Hf`) give them by `ghostMapElem_agree`, without the authority.
It does **not** hold for `V`'s half, `ghostVar γs.1 ½ V` (`ownRaftGhost`'s `Hvirt`).

`slot_open` (`StepGhost.lean:1341`) opens `slotInv` and reads `Hvirt` against the slot's own half
(`ghostVar_agree`) to learn `DurLe E V`: the entered maps lie below the node's virtual maps. That is
how a durable fragment (an entered vote or acknowledgement) is known to be in `V`. The steps that do
it are ordinary protocol steps:
- `vote_excl` (`StepGhost.lean:1472`) in `ownRaftGhost_step_stale` (`Refinement.lean:615`), `_app_accept`
  (`:2545`), `_snap_fastfwd` (`:3478`) and `_snap_restore` (`:3619`);
- `ownLogGhost_ack_agree` (`StepGhost.lean:1496`) and `ownLogGhost_hbResp` (`Refinement.lean:2366`) in
  `ownRaftGhost_step_heartbeat` (`:2392`); the traced heartbeat paths do the same
  (`TracedRaftStepRecvHb.lean:81`, `TracedRaftStepRecvUTHb.lean:52`, `ownRaftGhost_hbHigher`);
- `heartbeat_commit_le_last` (`Facts.lean:91`), from `raft__Step.lean:240` and the traced heartbeat;
- `ownLogGhost_not_doomed(_list)` (`Refinement.lean:2299`) and `rdOwn_arrive` (`:3921`) in the
  read-index steps (`ownRaftGhost_arrive`, `ownRaftGhost_single_confirm`);
- `slot_campK` (`StepGhost.lean:1415`) at the win (already an NC point).

With `V`'s half inside the crash invariant, as (b1) puts it, each of these steps must open that
invariant, and so needs `notCrashed`. NC then has to reach every ghost step, not five points:
- the generic `ownRaftGhost_stepC`/`ownRaftGhostR_stepR` and `StepGhostMode`'s lemmas;
- every `raft.Step` arm, whose ghost step runs at the arm's return, after `wp_apply` of the physical
  lemma (`raft__Step.lean:598` and so on). It can be done there by a lemma (sound, not yet proved):
  `WP e {{ v, |NC={E}=> Φ v }} ⊢ WP e {{ Φ }}` for a non-value `e`, since the last step holds the
  state interpretation;
- `node.run`'s and `RawNode`'s direct ghost steps (`InvNodeRun.lean:1516`, `TracedNodeRun.lean:900`, ...);
- in the traced instance, the heartbeat and append gates as well as the win's. So `HookGate`'s
  modality becomes NC everywhere, and every hook call site supplies it.

This is still route 1 and still sound. But (a)'s inventory and (c)'s estimate are wrong: the NC
plumbing row grows from ~16 files to essentially all of raft's step proofs, and the gates row from
the win's two gates to all of them.

Alternatives for the user to choose from (nothing implemented):
1. **Accept it.** NC goes through every ghost step, using the WP-post lemma above. This roughly
   doubles (c), mostly mechanical.
2. **Keep `V`'s half with the node.** Make the slot's virtual-map variable per generation: a fresh
   name per generation, recorded in `slotInv`, so a crash re-allocates both halves for `g + 1`
   without the dead node's half. The crash invariant then holds `slotLive 1 g` and the four
   authorities only, and `slot_open`'s readers need no NC. This changes `SlotNames`/`slotBody`,
   allocation, and the cut, enter, restart and stop proofs (`Enter.lean`, `Facts.lean`'s allocation).
3. **Variant (b3) first** (the four maps keyed by term in the winners' table), combined with 2. The
   crash invariant then holds only `slotLive`, and the win needs no NC either.

Also noted, for whichever is chosen:
- a stop must agree the crash names of the client's handle with those inside the run's
  `ownRaftGhost`. Two armed invariants of one id can be told apart with NC (both left disjuncts
  would hold the full `terms` authority) if the namespace includes the names;
- `NodeNames` is the natural carrier of the arm's names.

## (h) Option 2 of (g), decided and found not to remove the token (2026-11-21)

**Decision** (the coordinating session, 2026-11-21): option 2 of (g). The slot's virtual-map
variable gets a fresh ghost name per generation, recorded in `slotInv`, and the running node keeps
`V`'s half. A crash (or a stop) re-allocates the next generation's variable from the entered maps,
using `slotLive 1 g` from the crash invariant. The crash invariant holds `slotLive 1 g` and the
four leader-side authorities; the win and the trace update take `notCrashed` per (f). `NodeNames`
carries the crash names, and a stop checks the client's names against the run's. Option 3 / (b3)
is deferred as a later simplification that keeps the API.

**Finding** (the implementing session, before any Lean change). Option 2 does not let
`slot_open`'s readers do without `notCrashed`. What they need is not the half of `V` but the
relation between `V` and the **entered maps** `E` in `slotInv`: `DurLe E V`, used to look up a
durable fragment (an entered vote or acknowledgement) in `durShares ½ E`, then conclude it is in
`V`. A crash ends the generation, and the next one enters new batches into the same `E`, which
`V_old` does not contain. So a step of a thread of the dead generation (a zombie, which the logic
must cover: a ghost step lemma `P ={E}=∗ Q` is an entailment over all worlds, including those
after the crash) cannot get `DurLe E V`:
- with the name switched, its half no longer agrees with `slotInv`'s;
- with the old name's half frozen in `slotInv` at `V_old`, `DurLe E V_old` stops holding as soon as
  the next generation enters anything.

`E` is one authority shared across generations, so it cannot be frozen per generation either. The
general rule, sharpening (a)'s note on `notCrashed`: a thread needs `notCrashed` not only to
**update** state a crash rule may change, but also to **read** state that a later generation will
change. The entered maps are such state, and the ordinary steps listed in (g) read them.

So with any design in which the restarted node enters into the same entered maps, `slot_open`'s
readers need `notCrashed` regardless of where `V`'s half lives. The real choice is:
1. **(g)'s option 1:** NC through every ghost step. This needs the lemma
   `WP e {{ v, |NC={E}=> Φ v }} ⊢ WP e {{ Φ }}` for a non-value `e`, for the `raft.Step` arms whose
   ghost step runs at the return, and `HookGate` NC everywhere in the traced instance. Option 2's
   per-generation name then buys nothing, and `V`'s half can stay in the crash invariant as in (b1).
2. **Entered maps per generation** (route 2's direction: per-incarnation names for the promise
   authorities too). This needs new protocol reasoning about fragments across generations, (b2)'s
   cost and more.

Nothing implemented, no decisions.md or ledger entry: the decision of this section is not carried
out until one of the two is chosen.

## (i) Route 1, with the token through every ghost step (decided 2026-11-21)

**Decision** (the coordinating session, 2026-11-21, after (h)): route 1 as in (b1). The crash
invariant holds the six pieces of (a): `V`'s half, `slotLive 1 g` and the four leader-side
authorities. The node holds views of them. `notCrashed` is threaded through **every** ghost step,
the generic `ownRaftGhost_stepC`/`ownRaftGhostR_stepR` included, not only the five update points.
The win and the trace update are per (f). (h)'s per-generation name is dropped. (b3) remains a
later simplification that keeps the API.

The token reaches the steps as follows:
- through the crash-token update `ncfupd E P := notCrashed -∗ |={E}=> notCrashed ∗ P`
  (`GooseLang/NotCrashed.lean`);
- before a step, by `wp_ncfupd` (from `wp_notCrashed_acc`);
- at a function's return, by `wp_ncfupd_post`, proved: for a non-value `e`,
  `WP e {{ v, ncfupd E (Φ v) }} ⊢ WP e {{ Φ }}`. This covers `raft.Step`'s arms, whose ghost step runs
  after the physical lemma's `wp_apply`.

Proposed for Perennial in `notes/perennial-changes.md` ("notCrashed before a step").
