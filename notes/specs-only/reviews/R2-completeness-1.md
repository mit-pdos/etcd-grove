# R2 (raft's core, raft.go): completeness review, round 1

Reviewer: completeness, independent of the author. Read: `Spec/go_etcd_io/raft/v3/ApiCore.lean`, every
R2 spec file (`newRaft`, `raft__*`, `step*`, `getStatus`, `getBasicStatus`, `getProgressCopy`,
`RawNode__readyWithoutAccept`, `RawNode__acceptReady`, `need*/new*Storage*RespMsg`, the logger and
trace specs), R1's specs and laws that call into R2 (`Api.lean`, `NewRawNode`, `RawNode__*`,
`node__*`, `RawNode__Bootstrap`), the snippets `examples/specreq/raftcore/*.go`, the requirement
notes (`req/go_etcd_io_raft_v3*.md`), the pinned Go sources (`.lake/src/raft/{raft,node,rawnode,
status,bootstrap,logger,state_trace_nop}.go`), etcd's uses of raft status/logger
(`.lake/src/server/etcdserver/{raft,bootstrap,server}.go`), and the old specs and proofs
(`specs-ref`). I read `batch-R2.md` only after forming these findings (its "Left out" section is
answered under F7). Line numbers are of the pinned sources under `.lake/src/`.

## What is good

- **One `raft.Step` spec for every source** (`stepPre`/`stepPost` over `StepSrc`): the four
  `stepIn` cases match exactly what `RawNode`'s methods and `node.run`'s `recvc` arm hold (a received
  message's `msgSent`/credit/address, a local proposal with its updates, a local read with its
  `readCtx`, an unstamped report), and the post's error (`nil`, or `ErrProposalDropped` only for a
  `MsgProp`) is what `RawNode.Step`/`Propose`/`ProposeConfChange` and `node.run`'s `propErr` need.
  The glue at `rawnode.go:84`, `:91`, `:105`, `:124`, `:530`-`:556` is one `wp_apply`.
- `isReportType` and the report case need no `To`/`From` constraint, so `node.TransferLeadership`'s
  `To: lead` (`node.go:604`) and the ticks' `From: r.id` (`raft.go:873`, `:887`, `:903`) fit.
- **The getters** (`hasLeader`, `softState`, `hardState`, `getBasicStatus`, `getStatus`) are exact on
  the view and give fresh memory; `RawNode.Status`/`BasicStatus`/`node.Status` (R1) follow in one
  line each, and `NewRawNode`'s `prevSoftSt`/`prevHardSt` (`rawnode.go:57-59`) match
  `raftBoot_bind`'s fields.
- **`raft.applyConfChange.spec`'s premises are R1's `ApplyConfChange` premises verbatim** (plus 3h's
  `AsV2` law), so `rawnode.go:112` and `node.go:402` are glue-free.
- **`raftBoot`/`raftBoot_bind`** solve `newRaft` running before the `RawNode` exists without a
  bookkeeping handle in a client-facing statement.
- The `Ready` phases (`readyFresh`/`readyKept`/`readyHanded`/`rawNodeAt`) are the right shape for
  `node.run`'s stale send and for the second-`Ready`-before-`Advance` panic; R2 found R1's
  `RawNode.Ready` unsound and filed it (`req/go_etcd_io_raft_v3.md`, R2 item 1).
- `raftPeek` gives `id` and `logger` as discarded fractions, so `node.Tick`'s reads from client
  goroutines (`node.go:463`) are provable once the node invariant keeps a copy.

## Patterns of use

Every call into the `raft` struct from `node.go`, `rawnode.go`, `status.go` and `bootstrap.go`, and
what R1's spec at that call needs:

| # | pattern | call site | snippet | verdict |
|---|---|---|---|---|
| P1 | received message stepped (only a forwarded `MsgProp` may be refused) | `rawnode.go:124`, `node.go:399` | `ReqStepReceived` | covered |
| P2 | **received `MsgProp` stepped through `propc` with `From` rewritten to the node's id** | `node.go:385-389` (from `node.Step` → `stepWithWaitOption` → `propc`, `node.go:474-484`, `:516-523`) | none | **F1** |
| P3 | local proposal, normal or conf-change entries; dropped → `ErrProposalDropped` | `rawnode.go:91`, `:105`; `node.go:389` | `ReqStepPropose` (normal entry only) | covered; conf entries S6 |
| P4 | local read | `rawnode.go:556`, `node.go:399` | `ReqStepRead` | covered |
| P5 | reports: campaign, unreachable, snapshot status, transfer, forget | `rawnode.go:84`, `:530`, `:537`, `:542`, `:548`; `node.go:399` | `ReqStepReports` | covered |
| P6 | tick through the `tick` field | `rawnode.go:65`, `node.go:434` | `ReqTick` | covered |
| P7 | tick bypassing the state machine (`electionElapsed++`) | `rawnode.go:79` (`TickQuiesced`) | none | S3 |
| P8 | conf change applied, `Progress[r.id]` read before/after, `cs.Voters` scanned | `rawnode.go:112`, `node.go:401-427` | `ReqApplyConf`, `ReqFields` | covered |
| P9 | bootstrap: storage read, `becomeFollower(1)`, direct log append and commit, `applyConfChange` of every peer | `bootstrap.go:36-80` (`StartNode`, etcd's first start `etcdserver/bootstrap.go:599`) | none | **F5** |
| P10 | `Ready` computed, handed out, accepted | `rawnode.go:131-134`, `node.go:363`, `:435-436` | `ReqReadyAdvance` | covered; **F2**, **F4** |
| P11 | **raft fields read between computing a `Ready` and sending it** | `node.go:367-380` between `:363` and `:435` | none | **F4** |
| P12 | stale `Ready` sent when `HasReady()` is false | `node.go:353-364`, `:435` | `ReqReadyStale` | covered (depends on R1's `HasReady` request) |
| P13 | `Advance`: acknowledgements stepped, queue emptied; R1's post (applied, snapshot's configuration, driver) | `rawnode.go:477-490`, `node.go:444` | `ReqReadyAdvance` | **F2**, **F3** |
| P14 | construction around `newRaft`, `AsyncStorageWrites` read back from the config | `rawnode.go:51-61` | `ReqNewRawNode` | **F6** |
| P15 | status getters | `rawnode.go:494`, `:501`, `node.go:448` | `ReqStatus` | covered |
| P16 | progress visited with a callback | `rawnode.go:516-527` (`WithProgress`) | none | S3 |
| P17 | direct field reads by `node.run` (lead, term, id, logger, `hasLeader`, `Progress` filter) | `node.go:349-380`, `:395`; `rawnode.go:93`, `:121` | `ReqFields` | covered |
| P18 | concurrent reads of `id`/`logger` by `node.Tick` while `run` owns the struct | `node.go:463` | none | S4 |
| P19 | package logger set / used | etcd `etcdserver/raft.go:138`; `Config.validate` | `ReqLogger` | covered; default logger S2 |
| P20 | status as JSON (etcd's expvar `raft.status`) | `etcdserver/raft.go:55-63` → `Status.MarshalJSON` | none | S2 |

## First tier

### F1. A proposal received over the network cannot be stepped by `node.run` (`stepIn`)

A follower forwards a proposal (`stepFollower`, `raft.go:1743-1744`); at the leader, etcd's
transport calls `node.Step(ctx, m)` (R1: `msgSent γ m ∗ msgCredit γ m ∗ ⌜m.to = id⌝`), which sends any
`MsgProp` to `propc` (`node.go:516`, not `recvc`), and `node.run` overwrites `m.From = new(r.id)`
(`node.go:388`) before `r.Step(m)`. For `m' = {m with src := id}`, neither `stepIn` case can be
established: the first needs `msgSent γ m' ∗ msgCredit γ m'` (the caller has them at `m`, and no
law moves them across a change of `src`); the second needs `m'.term = 0`, `entries ≠ []`, the conf
entries decoding, and a `propUpd γ e` per entry, and no law extracts any of these from
`msgSent γ m ∗ msgCredit γ m`. This is every forwarded proposal in etcd (forwarding is on by default).
`stepLeader.lean`'s sketch even says "entries non-empty (`stepIn`, or the forwarder's `msgSent`)",
i.e. it assumes the first case, which the `From` rewrite breaks.

Fix (either): (a) state `stepIn`'s received case up to the sender for a proposal,
`∃ s, msgSent γ {m with src := s} ∗ msgCredit γ {m with src := s} ∗ ⌜m.to = id⌝` when
`m.type = MsgProp` (sound: `stepLeader`/`stepFollower` never read a proposal's `From` except to
forward); or (b) a law `msgSent_prop_local.spec : m.type = MsgProp → msgSent γ m ∗ msgCredit γ m ⊢
stepIn γ id {m with src := id}` (needs the realization of `msgSent`/`msgCredit` to carry the pure
facts and the updates). Add a snippet `ReqStepForwardedProposal` (`node.go:385-389`). The rewrite
also needs a field-write law on `msgPts` (S5).

### F2. `rawNodeAt_core` and `rawNodeAt_advance` do not compose: `Advance` is unprovable

`RawNode.Advance` (`rawnode.go:483-489`) reads `rn.stepsOnAdvance`, calls `rn.raft.Step(m)` for each
element (needs `raftCore r γ id ρ`), writes `rn.stepsOnAdvance[i] = nil` and finally re-slices the
field. `rawNodeAt_advance.spec` consumes `rawNodeAt` and gives the field, the messages and a wand
back to `rawNodeAt`, but no `raftCore` (nor `raftOf rn r`); `rawNodeAt_core.spec` gives `raftCore`
but also consumes `rawNodeAt`. Whichever is applied first, the other is unavailable until its wand
is closed, so the loop body has never both. `ReqReadyAdvance` (`ready.go`) is unprovable for the
same reason, and so are R1's `RawNode.Advance.spec` and `node.Advance.spec` (via `node.go:444`).

Fix: one law for the loop: `rawNodeAt_advance` also gives `∃ r ρ, raftOf rn r ∗ raftCore r γ id ρ`,
and its closing wand takes `raftCore r γ id ρ'` (any `ρ'`) with the emptied field.

### F3. R1's `Advance` post is not derivable from `ackPost`

R1's `RawNode.Advance.spec` (post) gives `appliedLb rn st.delivered.length` always, and with
`st.lastSnap = some s` the snapshot's configuration; its pre gives `confSkipped` only when
`st.lastSnap = none`. R2's acknowledgements are not tied to the driver `st` passed to `Advance`:
`ackOk rn γ m` mentions neither the batch nor `st`, and `ackPost` gives `appliedLb` only for an
apply response and the snapshot facts only for a message carrying a snapshot. Concretely:
- a batch with entries but no committed entries (no `MsgStorageApplyResp` queued,
  `rawnode.go:422-425`), or `adv = false` (empty queue): nothing gives
  `appliedLb rn st.delivered.length`;
- `st.lastSnap = some s`: nothing says a queued message carries `s` (or carries a snapshot at all),
  nor that `st.delivered.length = s.index` (`ackPost` gives `appliedLb rn s.index`, not at
  `st.delivered.length`);
- `st.lastSnap = some s` and an apply response queued: its `ackPre` needs `confSkipped`, which
  `Advance`'s pre does not supply (true in Go, since a batch with a snapshot has no committed
  entries, but unstated).

Fix: index the queue by what `Advance` holds, e.g. replace the per-message `ackOk` with a queue
predicate whose stepping is stated once: `rawNodeAt_advance` takes `nodeDriver rn γ st ∗ readyStor
rn none k [] ∗ nodeConf rn γ v ∗ (lastSnap none → confSkipped …)` and its closing wand gives exactly
R1's `Advance` post (applied lower bound, driver with `lastSnap := none`, the view or the snapshot's
configuration); or add a law `rawNodeAt rn γ id k false ∗ nodeDriver rn γ st ⊢ ⌜st.lastSnap = none⌝
∗ appliedLb rn st.delivered.length` and give `ackOk` the batch's snapshot (`ackOk rn γ st m` with
`m.snapshot = st.lastSnap` for the append response). Check against `ReqReadyAdvance` with a snapshot
batch and with an entries-only batch.

### F4. No read-only access to the raft struct while a `Ready` is fresh: `node.run` cannot hand one out

`node.run` computes `rd` (`node.go:363`: `readyFresh`), then reads `r.lead`, `r.hasLeader()`,
`r.logger`, `r.id`, `r.Term` (`node.go:367-380`) in the same iteration, then sends `rd`
(`node.go:435`), where `ready_handout.spec` needs `readyFresh`. The only access to `raftCore` is
`rawNodeAt_core` (needs `rawNodeAt`), so the reads first need `readyFresh_forget`, after which
freshness is gone (the R1 request for `HasReady` cannot help: `HasReady` is not called between the
reads and the send). Every `Ready` `node.run` sends goes through this.

Fix: `readyFresh_core.spec : readyFresh rn γ id k adv rd ⊢ ∃ r ρ, raftOf rn r ∗ raftCore r γ id ρ ∗
(raftCore r γ id ρ -∗ readyFresh rn γ id k adv rd)` (same `ρ`: the getters and `raftCore_peek` keep
it). Snippet: interleave `ReqFields`'s reads between `readyWithoutAccept` and the hand-out in
`ReqReadyStale` (or a new `ReqReadyPeek`).

### F5. `RawNode.Bootstrap` (etcd's first start) has nothing to stand on in R2

`StartNode` → `setupNode` → `rn.Bootstrap(peers)` (`node.go:258`; etcd: `etcdserver/bootstrap.go:599`)
calls into the raft struct directly: `rn.raft.raftLog.storage.LastIndex()` (`bootstrap.go:36`),
`rn.prevHardSt = emptyState` (`:47`), `rn.raft.becomeFollower(1, None)` (`:52`),
`rn.raft.raftLog.append(ents...)` (`:63`), `rn.raft.raftLog.committed = len(ents)` (`:77`) and
`rn.raft.applyConfChange(...)` per peer (`:79`). R1's `RawNode.Bootstrap.spec` cites R2 for these,
but: no law opens `rawNodeAt` to the log (R3's predicate), the storage or `prevHardSt`;
`becomeFollower.spec` needs `ρ.hs.term ≤ 1`, and nothing relates the view `rawNodeAt_core` returns
to the driver `Driver.start [] HardState.empty …` R1's pre holds; `applyConfChange.spec` needs
`deliveredLb rn γ l` with the entry delivered and the client's `confDecided` (R1's pre has neither:
the decisions are with the client after `cluster_alloc`), and Bootstrap applies the changes before
the entries are delivered (the application re-applies them later). No snippet covers it.

Fix: an internal spec for the bootstrap step stated at R2's level (e.g. a law
`rawNodeAt_bootstrap`: `rawNodeAt rn γ id 0 false ∗ nodeDriver rn γ (Driver.start [] …) ∗ bootLog γ
boot ∗ nodeConf rn γ ⟨0, ∅⟩` opens the fresh struct with its log at the empty storage and
`prevHardSt`, and closes after the boot entries are appended, committed and their `AddNode`s applied,
to `nodeConf rn γ ⟨|boot|, simple vs⟩`), or a raft-level `applyConfChange` precondition variant for
an entry of `bootLog` (one spec: the entry is delivered *or* in the bootstrap log, with the
cluster's bootstrap decision). Add `ReqBootstrap` (`bootstrap.go:32-81`).

### F6. `NewRawNode` cannot establish `asyncStorageWrites = false` from `newRaft`'s post

`NewRawNode` reads `config.AsyncStorageWrites` *after* `newRaft` (`rawnode.go:56`), and
`raftBoot_bind.spec` needs the field `false`. `newRaft.spec`'s post gives `c ↦ cv'` with no relation
to `cv` (`validate` writes `MaxUncommittedEntriesSize`, `MaxCommittedSizePerReady`,
`MaxInflightBytes`, `Logger`: `Config.validate.spec` states the relation exactly, but `newRaft`
drops it), so `ConfigOk cv`'s "AsyncStorageWrites off" does not reach the read.
Fix: `newRaft`'s post carries `validate`'s relation (`cv' = {cv with …}`), or at least
`cv'.AsyncStorageWrites' = cv.AsyncStorageWrites'`. (R1's `NewRawNode.spec` would benefit from the
same, so a client of `RestartNode` knows its config is untouched but for the defaults.)

### F7. Fifteen raft.go functions have no spec, all of them proved before, and the specified functions' proofs call them

The `raft.go` functions and their specs:

| function | spec | function | spec |
|---|---|---|---|
| `lockedRand.Intn` | yes | `hup` | yes |
| `StateType.String` | yes | `hasUnappliedConfChanges` | yes (post vacuous: F8) |
| `Config.validate` | yes | **`campaign`** | **no** |
| `newRaft` | yes | **`poll`** | **no** |
| `hasLeader`, `softState`, `hardState` | yes | `Step` | yes |
| **`send`** | **no** | `stepLeader`, `stepCandidate`, `stepFollower` | yes |
| `sendAppend`, `maybeSendAppend`, `maybeSendSnapshot` | yes | `logSliceFromMsgApp` | yes |
| **`sendHeartbeat`** | **no** | `handleAppendEntries`, `handleHeartbeat`, `handleSnapshot` | yes |
| `bcastAppend`, `bcastHeartbeat` | yes | `restore` | yes |
| **`bcastHeartbeatWithCtx`** | **no** | `promotable` | yes (post vacuous: F8) |
| **`appliedTo`**, **`appliedSnap`** | **no** | `applyConfChange` | yes |
| `maybeCommit` | yes | **`switchToConfig`**, **`loadState`** | **no** |
| **`reset`** | **no** | `pastElectionTimeout`, `resetRandomizedElectionTimeout` | yes |
| `appendEntry` | yes | `sendTimeoutNow`, `abortLeaderTransfer` | yes |
| `tickElection`, `tickHeartbeat` | yes | `committedEntryInCurrentTerm` | yes (post vacuous: F8) |
| `becomeFollower` | yes | **`responseToReadIndexReq`** | **no** |
| **`becomeCandidate`**, **`becomePreCandidate`**, **`becomeLeader`** | **no** | `increaseUncommittedSize`, `reduceUncommittedSize` | yes |
| | | `releasePendingReadIndexMessages` | yes |
| | | **`sendMsgReadIndexResponse`** | **no** |

All fifteen had specs *and proofs* in `specs-ref` (`Proof/go_etcd_io/raft/v3/raft__send.lean` 473
lines, `raft__switchToConfig.lean` 589, `raft__campaign.lean` 495, ..., no `sorry`; each linked in
`specs-ref`'s `Link.lean`). PRINCIPLES' "A smaller API is not a narrower scope" ("Do not leave out
any methods that we have verified previously") applies, and the user asked for every function. More
directly: the specified functions' proofs call them, and a proof sees only its callees' specs, so
these become unprovable as the branch stands: `raft.Step` (calls `send`, `appliedTo`, `appliedSnap`,
`raft.go:1170-1270`), `hup` (`campaign`), `stepCandidate` (`poll`, `becomeLeader`, `campaign`),
`stepFollower`/`stepLeader`/`handle*`/`sendAppend`/`maybeSendSnapshot`/`sendTimeoutNow`/`appendEntry`
(`send`), `becomeFollower` (`reset`), `newRaft` (`switchToConfig`, `loadState`), `applyConfChange`
(`switchToConfig`), `bcastHeartbeat` (`bcastHeartbeatWithCtx`), `releasePendingReadIndexMessages`
and `stepLeader` (`sendMsgReadIndexResponse`, `responseToReadIndexReq`). The sketches of
`stepCandidate`, `stepFollower`, `raft.Step` and `releasePendingReadIndexMessages` cite them by name.

The author's reason (`batch-R2.md`, "Left out": a guard only the caller's check establishes, which
would fix the realization) does not hold for most of them: PRINCIPLES' Scope says an internal
helper's spec "may simply mirror its code", and a spec over the function's *footprint* fixes only
the Go-level split of `raftCore` (fields, R3's log, R4's tracker), not the protocol ghost state.
What a meaningful spec with the caller's check as premise looks like, per function:

| function | panics / guard | premise naming the caller's check | post | meaningful? |
|---|---|---|---|---|
| `send(m)` | term set iff a vote type (`raft.go:518-541`); non-response not self-addressed (`:595`) | `⌜sendShape id m⌝` (every caller builds `m` so) | over its footprint (`id`, `Term`, `msgs`, `msgsAfterAppend`, `logger`): `m` (with `From`/`Term` filled) appended to the right queue; the message's justification is the caller's, when it closes `raftCore` | yes, as a footprint spec (the old one was) |
| `sendHeartbeat(to, ctx)` | `Progress[to]` non-nil | `ρ.role = Leader ∧ to ≠ id ∧ to ∈ ρ.prs` (`bcastHeartbeatWithCtx`'s visit) | `raftCore` kept | yes, same shape as `sendAppend.spec` |
| `bcastHeartbeatWithCtx(ctx)` | none | leader; `ctx` nil or the read-only queue's last context (what `bcastHeartbeat` passes) | `raftCore` kept | yes |
| `appliedTo(i, size)` | R3's `appliedTo` panics past `committed` | `i` is the last committed entry handed out (the apply ack, `appliedSnap`'s snapshot index): over R1's predicates as `ackPre` | `appliedLb rn i`; the auto-leave proposal (raft's own) | yes; this is where `ackPost`'s `appliedLb` comes from (F3) |
| `appliedSnap(s)` | `Restore` of the snapshot's `ConfState` panics if invalid (`raft.go:782-787`) | `snapValid γ s`, the snapshot written (`readyStor`) | the snapshot branch of `ackPost` (view at the snapshot's configuration) | yes |
| `reset(term)` | none | `ρ.hs.term ≤ term` (callers: higher term, `+1`, same) | view as in `becomeFollower`'s post, `lead = 0`, role unchanged | yes |
| `becomeCandidate` | panics at a leader (`raft.go:922`) | `ρ.role ≠ Leader` (hup's check) + the term receipt | term `+1`, vote `id`, candidate, no leader | yes |
| `becomePreCandidate` | panics at a leader (`:937`) | `ρ.role ≠ Leader` | pre-candidate, no leader, hard state unchanged | yes |
| `becomeLeader` | panics at a follower (`:953`); nil `Progress[r.id]` (`:966`); appendEntry refusal (`:982`) | `ρ.role ≠ Follower ∧ id ∈ ρ.prs` and `leaderOf γ ρ.hs.term id` (poll's won tally) | leader, `lead = id` | yes; it is where `leaderOf` (ApiCore) is consumed |
| `campaign(t)` | via `become*` | not a leader, and the campaign guard (promotable, no unapplied conf entry: hup's checks) | `raftCore` kept | yes, once the getters say what they check (F8) |
| `poll(id, t, v)` | none | the vote's `msgSent` (or the node's acknowledged self-vote) at the term | `VoteWon` at a candidate gives `leaderOf γ term id` | yes |
| `switchToConfig(cfg, trk)` | none in itself | `cfg`/`trk` are R4's restore/changer result for `m'` | `ConfState` listing `m'`, the tracker at `m'` | yes (R4 vocabulary) |
| `loadState(hs)` | commit outside `[committed, lastIndex]` (`raft.go:2039`) | over the fresh struct's log (R3) with `committed ≤ hs.commit ≤ last` (newRaft's `StorageHolds`) | term, vote, commit set | yes (a footprint spec: it runs before `raftCore` exists) |
| `responseToReadIndexReq(req, i)` | `Entries()[0]` for a local request (`:2079`) | `(req.src = 0 ∨ req.src = id) → req.entries ≠ []` | local: read state queued; else a `MsgReadIndexResp` to `req.From` at `i` | yes |
| `sendMsgReadIndexResponse(r, m)` | none (`ReadOnlySafe`) | leader, an entry of the term committed (the caller's `committedEntryInCurrentTerm`), `m` a read (`stepIn` or a forwarded `msgSent`) | `raftCore` kept | yes, once F8's getter says it |

Fix: specify the fifteen (and, for the footprint ones, add an internal split law
`raftCore r γ id ρ ⊣⊢ ∃ …, <fields> ∗ <rest>` in `ApiCore.lean`, marked internal), rather than leave
the question open (`batch-R2.md`, open question 3: the user's standing answer is "all functions").

### F8. The guard getters' posts are vacuous, so their callers cannot get the guards

`raft.promotable.spec`, `raft.hasUnappliedConfChanges.spec` and
`raft.committedEntryInCurrentTerm.spec` return `b` with only `raftCore` (no relation of `b` to
anything). Their callers branch on `b` for safety: `hup` (`raft.go:997`, `:1001`: the campaign
guard its own sketch relies on), `stepLeader`'s read index (`committedEntryInCurrentTerm` before
answering a read, `raft.go:1375`: the classic read-index condition) and `releasePendingReadIndexMessages`
(`raft.go:2134`). With these posts the callers' proofs get nothing from the check. PRINCIPLES: "the
postcondition says what the caller inspects". Fix: posts that say what the result means over a
fact the caller can pass on (e.g. `b = true -∗ termCommitted r γ ρ.hs.term` persistent, or the
internal split's record fields), as the premises of `campaign`/`sendMsgReadIndexResponse` in F7 name.
(`pastElectionTimeout` and `increaseUncommittedSize` are liveness or size checks; their vacuous
posts are fine.)

## Second tier

- **S1. Async-storage helpers** (`needStorageAppendMsg`, `newStorageAppendMsg`,
  `newStorageApplyMsg`; `rawnode.go:200`, `:223`, `:372`): R1 asked for them (req item 1). They are
  dead under `ConfigOk`, but they are pure message builders with no panic; a mirror spec over
  `raftCore` like `newStorageAppendRespMsg.spec` costs nothing and keeps "every function". Specify.
- **S2. The logger and the status formatting.** `getLogger.spec`'s `loggerOk` and
  `ResetDefaultLogger`'s sketch rest on `*DefaultLogger` meeting `loggerOk` (the initial `raftLogger`,
  `logger.go:61-66`), which needs `DefaultLogger`'s methods (`logger.go:78-142`; `Output` on Go's
  `log.Logger`) or at least a stated law `defaultLogger_loggerOk.spec` with its trust boundary named.
  `Status.MarshalJSON` has a user in etcd (expvar `raft.status`, `etcdserver/raft.go:55-63`, through
  `encoding/json`; R1's P18/S5 noted it) and `Status.String` calls it with a `Panicf` guard: specs
  with `err = nil` are meaningful (reads `statusOwn`'s progress map). `header`, `EnableTimestamps`,
  `EnableDebug`: trivial mirror specs.
- **S3. `TickQuiesced` and `WithProgress` reach into the struct with no R2 law.** `rawnode.go:79`
  writes `rn.raft.electionElapsed`; `rawnode.go:517` calls `rn.raft.trk.Visit` with a callback that
  copies each `Progress`. Neither has an R1 spec yet, and neither can get one without an R2 law (an
  `electionElapsed` bump keeps `raftCore`; a read-only tracker view for `Visit`, R4's predicate).
  Add the laws (or raft-level helpers) and tell R1.
- **S4. Concurrency of `node.Tick`'s reads** (`node.go:463`, from any goroutine while `run` holds
  `raftCore`): provable from `raftPeek`'s discarded fractions, but nothing records that the node
  invariant must keep them; add a snippet (`ReqTickMissed`) so the pattern stays covered.
- **S5. Field writes on `msgPts`**: `node.go:388` (`m.From = new(r.id)`), `raft.go:1743`, `:1762`,
  `:1784` (`m.To = new(r.lead)`) need a write law for a message's `From`/`To`; `req/…_raftpb.md`'s
  "from R2" asks only for splitting off a snapshot and entries. Add it to the 3h request.
- **S6. Snippet gaps besides F1/F4/F5**: `ReqStepPropose` proposes only a normal entry; the
  conf-change proposal (`rawnode.go:101-105`, `confChangeToMsg`) is where `stepIn`'s decode
  premise is needed, so add one. `ReqStepReports` builds `MsgTransferLeader` without `To`; the node
  path sets `To: lead` (`node.go:604`): add it so the report case's lack of a `To` constraint stays
  tested.
- **S7. Citations.** Most `rawnode.go`/`node.go` line numbers in the specs and snippets are off
  (they do not match the pinned `565c2bd`): e.g. `RawNode.Step` is `rawnode.go:116-125` (cited
  `:140`), `Propose` `:90-96` (`:85`), `Advance` `:477-490` (`:451`), `ReadIndex` `:555-557`
  (`:521`), `Tick` `:64-66` (`:73`), `ApplyConfChange` `:111-113` (`:121`), `Status` `:493-496`
  (`:460`); `node.go`'s `propc` arm is `:385-393` (cited `:384`), `recvc` `:394-399` (`:392`), `confc`
  `:400-427` (`:399`), `tickc` `:433-434` (`:416`), `readyc` `:435-442` (`:419`), `status` `:447-448`
  (`:425`). The "Users" lines of `raft__sendTimeoutNow`, `raft__bcastHeartbeat`, `raft__sendAppend`,
  `raft__maybeSendAppend`, `raft__maybeSendSnapshot`, `raft__bcastAppend` are one copied sentence
  ("`stepLeader`, `becomeLeader`, `switchToConfig`, `tickHeartbeat` (via `MsgBeat`), each other") that
  is wrong for most of them (`sendTimeoutNow` is called only by `stepLeader`, `raft.go:1590`, `:1677`;
  `bcastHeartbeat` by `stepLeader` and `sendMsgReadIndexResponse`, `:1297`, `:2165`).

## Go code

No new bug. Checked and ruled out: `becomeLeader`'s `Progress[r.id]` dereference (`raft.go:966`)
needs a candidate removed from its configuration mid-campaign, which `hup`'s unapplied-conf-change
check and the absence of commits during a candidacy exclude (the premise F7 proposes records it);
`responseToReadIndexReq`'s `Entries()[0]` is reached only for local reads, which carry one entry.

## Ranking of the targets by need of revision

1. **`ApiCore.lean`'s `RawNode` laws** (F2, F3, F4, F5): `Advance`, `node.run`'s hand-out and
   `Bootstrap` are unprovable from them; `rawNodeAt_advance` and the acknowledgement interface need
   restating against R1's `Advance`.
2. **The missing helper specs and the getter posts** (F7, F8): fifteen previously proved functions,
   without which `raft.Step`, `hup`, `step*`, `becomeFollower`, `newRaft`, `applyConfChange` have no
   callee specs to be proved from.
3. **`stepIn` / `raft__Step.lean`** (F1): one case to widen (or a law), plus a snippet.
4. **`newRaft.lean`** (F6): one conjunct in the post.
5. Snippets (S4, S6, and those of F1, F4, F5), the logger/status/async helpers (S1, S2), the
   `TickQuiesced`/`WithProgress` laws (S3), citations (S7).
6. Fine as they are: `getStatus`, `getBasicStatus`, `getProgressCopy`, `hasLeader`, `softState`,
   `hardState`, `applyConfChange` (but for F5's bootstrap path), `readyWithoutAccept`, `acceptReady`,
   `tickElection`/`tickHeartbeat`, `SetLogger`, the trace hooks.

## Verdict

Not done. The `raft.Step` design (one provenance precondition, one error) serves every caller but
the forwarded proposal (F1), and the getters serve R1 exactly. But the `RawNode`-phase laws do not
support the two loops they exist for (`Advance`, F2/F3; `node.run`'s hand-out, F4) nor the bootstrap
path (F5), `newRaft`'s post loses a fact `NewRawNode` reads (F6), and fifteen previously proved
helpers are left without specs while the specified functions' proofs depend on them, two of whose
guards the getters' vacuous posts cannot supply (F7, F8). A second round is needed.
