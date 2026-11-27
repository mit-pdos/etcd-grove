# T10 step 3 (B), option (a): what `NewServer_dist` and `Serve_dist` assert, before and after

For the etcd_safe lead's ruling of 2026-11-27 (#50): every change to what `etcd_dist.NewServer_dist.wp_proof` or
`etcd_dist.Serve_dist.wp_proof` asserts is trusted. A **weaker** change (trust shrinks) is pre-approved and recorded
here as approved; a **stronger** or **incomparable** one needs a fresh adversarial review and then Upamanyu, and nothing
is built on it beyond the draft.

- **Today** = `7ff538e61d` (Handoff T10s3b-4, before any (B) definition change). **With this change** = `66991db961`
  (Handoff T10s3b-10, branch `etcd-safe-t10s3b-a/2026-11-27`).
- Neither axiom's text changes (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/{NewServerDist,ServeDist}.lean`
  and `ServerOn.lean`, `InvBuild.lean` are identical at both commits). What changes is the Proof-tier definitions the
  statement unfolds to: `InvRaftNode.lean` (below `IRN` = `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRaftNode.lean`)
  and the new `NotifyCD.lean`. The reached set is Lean's, not grep's: `/shared/tmp/t10s3b-chk/AxCheck6.lean`,
  output `out6c.txt` (149 axioms; only these four reach a changed definition: `NewServer_dist`, and through
  `RNNames` only, `NewPeerHandler_dist`, `Serve_dist`, `PeerServe_dist`).
- Go: the etcd fork at the pin of `etc/goose.py` (project `etcd`, `rev=251a430ce042`; read with
  `git -C /shared/etcd show 251a430ce042:server/etcdserver/raft.go`, the main tree's `.lake/go-src/etcd` is at a later
  commit), raft at the pin `565c2bd`.

## Summary

| # | Definition (step) | Axiom | Direction in the axiom | One line |
| --- | --- | --- | --- | --- |
| 1 | `rnApN`: replay job moved from the payload into `notifyc`'s first deposit (`isNotify` → `isNotifyD`) (B3 part 1) | `NewServer_dist` | **equivalent** (in general: incomparable) | channel payload inside an invariant, so incomparable in general; but the post fixes `γrn.a0 = []`, which makes `rnReplayJob ⊣⊢ True`, and `isNotifyD _ _ True R ⊣⊢ isNotify _ _ R` |
| 2 | `rnApSnap`: second `notifyc` deposit `True` → `rnReplayJob …` (B5 step 1) | `NewServer_dist` | **equivalent** (in general: incomparable) | same: `rnReplayJob ⊣⊢ True` at `a0 = []` |
| 3 | `RNNames` gains the label `s0` (B3 part 2) | `NewPeerHandler_dist`, `Serve_dist`, `PeerServe_dist` | **equivalent** | they read no definition that reads `s0` |
| 4 | `RNNames.s0`, `rnLoopTok`/`rnLoopTokP` (driver at `γ.s0` instead of `∃ S`), `rnWorkerStartTok`'s seed `rnReplayState γ terms snap0` → `rnReplayHist γ terms γ.s0 snap0` (B3 part 2) | `NewServer_dist` | **stronger** | the post newly says that the replay seed covers every entry of the driver's durable state above `snap0` (the same `S` the loop's driver is at) |
| 5 | `rnReplayHist` drops `replayPending runs γ.a0 n` (B6 part 1) | `NewServer_dist` | **weaker** (in this axiom: equivalent) — **weaker: pre-approved by the lead 2026-11-27 (#50)** | one pure conjunct less in a positive position; at `a0 = []` it was `replayLayout runs`, which `replayHistoryMatches` keeps |
| net | rows 1-5 together, Today vs 66991db961 | `NewServer_dist` | **stronger** (row 4 alone) | rows 1, 2, 5 are equivalences in this axiom; row 4 adds the coverage claim |
| 6 | `rnRestartOk` (B6, not yet changed) | `NewServer_dist` | expected **weaker** (equivalent at `a0 = []`) | positive conjunct of `isRaftNode`; dropping `|a0| ≤ commit0` |
| 7 | `rnStopImage` (B7, not yet changed) | `NewServer_dist` | expected **incomparable** | inside `inv rnStopN (rnStopImage γ ∨ token γ.sc)` |
| 8 | `wal.stopImage` (B7, not yet changed) | `Serve_dist` | expected **incomparable** | inside `srvDoneInv`'s `inv srvStopN (srvDiskImage … ∨ token c)` |

**For the reviewer, first:** row 4 (the only strengthening at `66991db961`), and the premise all the
"equivalent" verdicts rest on, `γn.a0 = []` in `srvBuiltG`'s `%HEr` (`ServerOn.lean:182`). If a dist axiom that reaches
these definitions without `a0 = []` lands (a restart or crash-restart `NewServer` axiom, e.g. B4's
`NewServerC_dist` on `etcd-safe-crash-b4r/2026-11-26`), rows 1, 2 become incomparable and row 5 strictly weaker there,
and each needs its own review.

## Where the definitions occur in `NewServer_dist` (polarity)

`NewServer.specG_dist` (`Spec/…/dist/NewServerDist.lean:59`) is a Hoare triple; none of the changed definitions occurs in
its precondition (lines 59-270; the `rn*`/`RNNames` names appear only in the post, from line 275). The post
(`NewServerDist.lean:271-331`) is `(fail) ∨ (⌜err = nil⌝ ∗ … ∃ … (γrn : RNNames GF) … , … ∗ srvBuiltG … γrn … ∗ …)`
(γrn bound at line 275, `srvBuiltG` at 288): **positive**, and γrn is **existential**. In `srvBuiltG`
(`ServerOn.lean:163`, same at both commits) the relevant conjuncts are plain `∗`-conjuncts:

- `ServerOn.lean:178` `"#Hrn" ∷ isRaftNode Er γn (srvRAddr s)`;
- `ServerOn.lean:179-182` `"%HEr" ∷ ⌜… ∧ (… ∧ γn.pre = [] ∧ …) ∧ γn.a0 = []⌝`;
- `ServerOn.lean:202` `"Hloop" ∷ rnLoopTok γn [] ∗ … ∗ "Hrdone" ∷ rnWorkerStartTok γn (srvRAddr s)`.

Below those: `isRaftNode` (`IRN:2683`, persistent, plain conjuncts) holds `"#Hrok" ∷ rnRestartOk γ` (positive) and
`"#Hapci" ∷ isRNApplyc E γ apc`; `isRNApplyc` (`IRN:2564`) is `isSspsc γ.ap c (rnApP E γ) …`, a channel **invariant**
whose payload predicate the sender gives and the receiver gets: `rnApP` (`rnApN ∨ rnApSnap`) and everything inside it is
in **both polarities** (an invariant's content is neither monotone nor antitone). Inside `rnApN`/`rnApSnap`, `notifyc`'s
`isNotify`/`isNotifyD`/`isNotify2` are invariants again (both polarities). `rnWorkerStartTok` and `rnLoopTok` are not under
any invariant or wand: **positive**. `rnStopImage` is in `rnDoneEsc` (`IRN:2666`), `inv rnStopN (rnStopImage γ ∨ …)`,
the close resource of `done` in `isRaftNode`: both polarities. No changed definition is reached on the left of a wand.
(Only the definitions' text was searched for other occurrences; `AxPath.lean` printed one path per target. A
per-occurrence dump would make this mechanical.)

The fact that turns the invariant rows into equivalences: at `γn.a0 = []`,

- `rnReplayJob γ terms rt n` (`IRN:2424`, unchanged) is `□ ∀ sm ci, ⌜… ∧ n < γ.a0.length ∧ …⌝ -∗ …`; with
  `γ.a0.length = 0` the premise is `⌜False⌝`, so `rnReplayJob … ⊣⊢ True`;
- `replayPending runs γ.a0 n` (`ReplayModel.lean:42`, unchanged) is `replayLayout runs ∧ ∀ ci, n < A.length → …`; at
  `A = []` it is `replayLayout runs`;
- Iris's `IProp` is affine (`P ∗ True ⊣⊢ P`), and `inv N`, `∗`, `∃`, `□` respect `⊣⊢`, so a `⊣⊢` inside an invariant
  gives `⊣⊢` of the invariant. γrn is existential and `⌜γn.a0 = []⌝` is a conjunct beside the occurrences, so the
  rewrite applies under the `∃`.

## Row 1: `rnApN` (B3 part 1) — equivalent in `NewServer_dist`

Today (`7ff538e61d`, `IRN:2345`), the relevant conjuncts:

```lean
    (∃ γnc : NotifyNames, isNotify γnc ap.notifyc' (rnApR γ F ce) ∗ notifyRcv γnc) ∗          -- IRN:2350
    …
    rnRtOk γ ap.raftTerm' (rnLogOf γ (F ++ ce)).length ∗
    rnReplayJob γ ap.replayTerms' ap.raftTerm' (rnLogOf γ (F ++ ce)).length)                  -- IRN:2368
```

With this change (`66991db961`, `IRN:2444`):

```lean
    (∃ γnc : NotifyNames, isNotifyD γnc ap.notifyc'                                           -- IRN:2451
      (rnReplayJob γ ap.replayTerms' ap.raftTerm' (rnLogOf γ (F ++ ce)).length) (rnApR γ F ce) ∗
      notifyRcv γnc) ∗
    …
    rnRtOk γ ap.raftTerm' (rnLogOf γ (F ++ ce)).length)
```

`isNotifyD` (new, `NotifyCD.lean:37-53`) is `NotifyC.lean`'s `isNotify` (`NotifyC.lean:61`, unchanged) with one more
deposit, at state `(1, false)`:

```lean
def notifyMatch (R) s : Nat → Bool → IProp GF          -- NotifyC.lean     def notifyDMatch (Q R) s : …     -- NotifyCD.lean:37
  | 1, false => iprop(⌜s = .Buffered [()]⌝)                                 | 1, false => iprop(⌜s = .Buffered [()]⌝ ∗ Q)
```

(the other three states, `notifyDInv`/`notifyInv` and `isNotifyD`/`isNotify` are token-identical otherwise:
`isChan ch γ.ch Unit ∗ ⌜cap = 1⌝ ∗ inv nroot (…Inv γ …)`, same `NotifyNames`, same `notifyRcv`).

**Where:** `NewServer_dist` post → `srvBuiltG` → `isRaftNode` → `isRNApplyc` (sspsc invariant) → `rnApP` → `rnApN`.
Both polarities (channel payload).

**Direction.** In general incomparable: the sender's obligation moves (the job is no longer due at the `applyc` send,
but is due at the first `notifyc` send) and the receiver gets the job later; `isNotifyD` and `isNotify` are different
invariants. **In this axiom, equivalent:** `rnReplayJob … ⊣⊢ True` (a0 = []), so Today's conjunct is `True`, and
`notifyDMatch True R s n b ⊣⊢ notifyMatch R s n b` pointwise, hence `isNotifyD γnc c (rnReplayJob …) R ⊣⊢ isNotify γnc c R`.
Not weaker-and-pre-approved but equal; recorded so that the review confirms the `a0 = []` argument.

**Faithful to the Go** (`server/etcdserver/raft.go` at `251a430ce042`): the loop builds `ap` with `replayTerms: terms`
and `raftTerm` (lines 230-247) and sends it on `applyc` (252) **before** the WAL `Save` (276); `notifyc :=
make(chan struct{}, 1)` (230) is sent on after the `Save`: a follower after `processMessages` (316, 319), a leader at
once (344), a second time on a conf change (334, 351), and for a snapshot after `SaveSnap`/`Sync` (269, 296). The apply
thread reads `apply.replayTerms` only after `<-apply.notifyc` (`server.go:995`, then the merge at 1013). So evidence
deposited at the first `notifyc` send is available exactly where the Go code reads the field; the field's value is
fixed in `ap` at the `applyc` send, as before.

## Row 2: `rnApSnap` (B5 step 1) — equivalent in `NewServer_dist`

Today (`IRN:2382`), `notifyc`'s two-send protocol, second deposit:

```lean
    (∃ γnc : NotifyNames, isNotify2 γnc ap.notifyc'
      iprop(∃ (j : Nat) (m : SnapshotMetadataM), walSnapRec γ.wal.h j m ∗ ⌜m.Index' = sv.Metadata'.Index'⌝)
      iprop(True) ∗ notifyRcvN γnc 0) ∗                                                        -- IRN:2408
```

With (`IRN:2484`):

```lean
      (rnReplayJob γ ap.replayTerms' ap.raftTerm' (rnLogOf γ A').length) ∗ notifyRcvN γnc 0) ∗   -- IRN:2512
```

(`isNotify2`, `NotifyC2.lean:54`, unchanged.)

**Where:** as row 1 (`rnApP`'s second disjunct). Both polarities.

**Direction.** In general incomparable (the second sender must now give the job; `applyAll`'s receive gets it). In this
axiom **equivalent**: `rnReplayJob … ⊣⊢ True` at `a0 = []`, so the invariant is the same up to `⊣⊢`.

**Faithful:** the snapshot `Ready`'s two sends (`raft.go:296` after `SaveSnap`/`Sync`, then 319 or 344); `applySnapshot`
receives once (`server.go:1060`) and `applyAll` once (995), and reads `apply.replayTerms` after its own receive (1013).
The job is made at the *enter* (after the `applyc` send, `rnReplayJob_of_lead`) and deposited at the second send.

## Row 3: `RNNames.s0` for `NewPeerHandler_dist`, `Serve_dist`, `PeerServe_dist` — equivalent

Today `structure RNNames` (`IRN:99`) has `a0` (121) … `snap0` (131); with this change (`IRN:100`) it also has

```lean
  s0 : RaftState                                                                                -- IRN:136
```

**Where:** these three axioms reach `RNNames` and none of `rnLoopTok`, `rnWorkerStartTok` (`out6c.txt`), the only
definitions that read `.s0` (`IRN:2603`, `IRN:2746`; the other `.s0` reads are in `Spec`/proof files no axiom reaches).

**Direction: equivalent.** Whether γ is bound by `∀` or `∃`, a statement that reads no `s0` is the same over the old
structure and over the new one (the projection forgetting `s0` is onto). Faithful: a label; no Go state is described.

## Row 4: the driver's durable state `s0`, and the seed that describes it (B3 part 2) — **stronger**

Today:

```lean
-- IRN:2475-2476 (rnLoopTokP), IRN:2497-2498 (rnLoopTok)
def rnLoopTokP (γ) (L) (p : HardStateM) (b : Bool) : IProp GF :=
  iprop(∃ (sent …) (cums …) (S : RaftState) (r : StateType), rnDrv γ L p S r ∗ … ∗ rnWalView γ ⟨S, p, none, …⟩ ∗ …)
def rnLoopTok (γ) (L) := iprop(⌜γ.snap0 ≤ (rnLogOf γ L).length⌝ ∗ ∃ p : HardStateM, rnLoopTokP γ L p false)
-- IRN:2639-2640, IRN:2155-2156
def rnWorkerStartTok (γ) (r) :=
  iprop(rnDoneTok γ r ∗ ∃ terms : GoSlice, rnReplayTermsAddr r ↦ terms ∗ rnReplayState γ terms γ.snap0)
def rnReplayState (γ) (view) (n) := iprop(∃ runs, view ↦*□ runs ∗ ⌜replayPending runs γ.a0 n⌝)
```

With this change:

```lean
-- IRN:2580 (rnLoopTokP: S now a parameter, the same body), IRN:2602-2603
def rnLoopTokP (γ) (L) (p : HardStateM) (b : Bool) (S : RaftState) : IProp GF :=
  iprop(∃ (sent …) (cums …) (r : StateType), rnDrv γ L p S r ∗ … ∗ rnWalView γ ⟨S, p, none, …⟩ ∗ …)
def rnLoopTok (γ) (L) := iprop(⌜γ.snap0 ≤ (rnLogOf γ L).length⌝ ∗ ∃ p : HardStateM, rnLoopTokP γ L p false γ.s0)
-- IRN:2745-2746, IRN:2196-2198 (after row 5)
def rnWorkerStartTok (γ) (r) :=
  iprop(rnDoneTok γ r ∗ ∃ terms : GoSlice, rnReplayTermsAddr r ↦ terms ∗ rnReplayHist γ terms γ.s0 γ.snap0)
def rnReplayHist (γ) (view) (S) (n) := iprop(∃ runs, view ↦*□ runs ∗ ⌜replayHistoryMatches runs S n⌝)
-- ReplayHistory.lean:60 (unchanged)
def replayHistoryMatches rs S n := replayLayout rs ∧
  ∀ ci t, n < uint.nat ci → plogTermAt S.base S.ents ci = some t → ∃ r ∈ rs, replayContains r ci t
```

**Where:** `rnLoopTok γn []` and `rnWorkerStartTok γn …` are plain conjuncts of `srvBuiltG` (`ServerOn.lean:202`):
positive, under the post's `∃ γrn`.

**Direction: stronger.** Under `a0 = []` (and `snap0 = 0`, which `rnRestartOk` gives at `a0 = []`: either disjunct),
Today's post has `∃ γrn, … (∃ p, ∃ S, rnLoopTokP-body at S) ∗ (∃ terms runs, … ∗ ⌜replayLayout runs⌝)`; the new one has
`∃ γrn (with s0), … (∃ p, rnLoopTokP γ [] p false γ.s0) ∗ (∃ terms runs, … ∗ ⌜replayLayout runs ∧ every entry of γ.s0
above snap0 has its term in runs⌝)`. New ⊢ Today (take `S := γ.s0`; drop the coverage). Not conversely: Today says
nothing relating the seed to the driver's durable state. So the axiom now additionally asserts: **at `NewServer`'s
return, the `initialReplayTerms` slice covers, with the right term, every entry above `snap0` of the durable raft state
the loop's driver starts from.**

**Faithful to the Go:** on a first start (`bootstrappedRaft.newRaftNode`, `bootstrap.go:645-652` at `251a430ce042`)
`len(b.peers) != 0`, so `terms` stays `nil` and `raft.StartNode(b.config, b.peers)` is called; the seed is empty. The
durable state the driver starts from has no entries: the WAL was just created with metadata only (`bootstrapNewWAL`,
`bootstrap.go:764-771`), and raft's `Bootstrap` puts the bootstrap conf changes in the *unstable* log
(`rn.raft.raftLog.append(ents...)`, raft `bootstrap.go:63`, at `565c2bd`), not in `Storage`; they become durable only at
the loop's first `Save` (`raft.go:276`), after `NewServer` returns. In Lean, `bootstrappedRaft.newRaftNode.spec` fixes
`γw.s0 = (bt.view γr).S` and the premise `raftState γ.cl id RaftState.init`; `replayHistoryMatches_init`
(`ReplaySeed.lean:69`) proves `replayHistoryMatches [] RaftState.init n`. (On a restart the seed is
`replayTermsFromStorage` of the WAL's entries above its snapshot, `snapshot_terms.go:25-32`, `replaySeed_history`; not
reached by this axiom, whose post is a first start.) The in-process `NewServer.wp_proofG` proves the same post over the
same definitions (`NodeStartLinked.lean:202` builds the seed).

**What an adversarial reviewer should try.** A Go execution in which, when `NewServer` returns on a fresh member, the
node's durable state (what `rnDrv`/`rnWalView` and raft's `raftState` mean by it) already holds an entry above index 0:

1. a path in `NewServer`/`bootstrap` for a new cluster that writes entries to the WAL or `MemoryStorage` before the raft
   loop starts (`bootstrapNewClusterNoWAL`, `wal.Create`, `MemoryStorage.Append`/`ApplySnapshot` in `bootstrap`);
2. raft's `StartNode` making the bootstrap entries part of what the node API's model calls durable (`raftState`) rather
   than unstable — e.g. the model's `StartNode` spec moving `raftState` off `RaftState.init`;
3. a configuration that reaches `StartNode` with a non-empty `MemoryStorage` (a WAL directory that exists:
   excluded by `wal.bootRes cfg`, the precondition's fresh WAL; check it really is);
4. `snap0 ≠ 0` with `a0 = []` (would shift the coverage window): `rnRestartOk`'s two disjuncts both give `snap0 = 0`.

## Row 5: `rnReplayHist` drops `replayPending` (B6 part 1) — **weaker: pre-approved by the lead 2026-11-27 (#50)**

Between B3 part 2 and B6 part 1 (`IRN:2191-2193` at `7ff538e61d`, where it was not yet reached by the axiom):

```lean
def rnReplayHist (γ) (view) (S) (n) := iprop(∃ runs, view ↦*□ runs ∗
    ⌜replayPending runs γ.a0 n ∧ replayHistoryMatches runs S n⌝)
```

With this change (`IRN:2196-2198`): `⌜replayHistoryMatches runs S n⌝` alone.

**Where:** through `rnWorkerStartTok` only (`IRN:2746`), positive (row 4). (`rnReplayHistP`, `IRN:2312`, is not
reached.)

**Direction: weaker** (a pure conjunct less in a positive position); in this axiom **equivalent**, since at `a0 = []`
`replayPending runs [] n` is `replayLayout runs`, which `replayHistoryMatches` contains. Approved as weaker by the lead's
rule (2026-11-27, #50). It does not offset row 4: row 4's strengthening is the coverage conjunct, which stays.

**Faithful:** the dropped statement (while the cursor is below `|a0|`, the backend's last term is in a run) is still true
of `initialReplayTerms` (`replaySeed_pending`, kept), merely no longer asserted.

## Rows 6-8: not yet changed at `66991db961` (to classify when made)

- **`rnRestartOk`** (B6; `IRN:579` Today, `IRN:584` now, identical): `⌜a0 = [] ∧ t0 = 0 ∧ commit0 = 0 ∧ snap0 = 0⌝ ∨
  (⌜pre = [] ∧ snap0 ≤ |a0| ∧ |a0| ≤ commit0 ∧ ¬ clusterNoSnap⌝ ∗ …)`. Positive (`isRaftNode`'s `#Hrok`). Dropping
  `|a0| ≤ commit0` is **weaker**; at `a0 = []` equivalent. Pre-approved under the rule when made.
- **`rnStopImage`** (B7; `IRN:2544` Today, `IRN:2649` now, identical): inside `rnDoneEsc`'s invariant: dropping
  `i ≤ σ.commit` is **incomparable** in general (the loop's `onStop` deposits less, the stop's caller takes less).
  Reviewer: a Go stop (or crash then restart) whose image has `i > σ.commit` and a client of the axiom that relied on the bound.
- **`wal.stopImage`** (B7, `Serve_dist` via `memberUpL → srvStopRight → srvDoneInv → srvDiskImage → srvDiskImageAt`):
  inside `srvDoneInv`'s invariant (`InvRestart.lean:325`): **incomparable** in general. Same review.

## The `bootLen` premise (B8), ruled 2026-11-27

B8's case `i < bootLen` needs `bootLen ≤ σ.commit` (d6, session 3 item 2). The lead ruled: use the premise
`γ.cl.bootLen = γ.boot.length` as in B4 rev 3 (C-I2/C-I2-K, met from `#Hsrl`/`srvClusterOk`; branch
`etcd-safe-crash-b4r/2026-11-26` @ `700f58c79f`, `notes/etcd-dist-b4.md` §R3.1, finding K-4), so there is one form.
Recorded in `notes/etcd-dist-d6.md` at B8's item.
