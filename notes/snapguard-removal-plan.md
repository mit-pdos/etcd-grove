# Removing the merged snapshot's index guard (plan, 2026-11-20)

## Replay metadata and the recovered commit

This branch pins etcd `1e59f9f173ea`, which includes the RangeStream fix
at `4416a5786` and the replay repair at `03c73a97acff`. When the backend is ahead of the
apply cursor, the sender labels its snapshot with the index, entry term
and configuration of the frozen database. A pre-3.5 backend can lack the
term and configuration. Bootstrap recovers the configuration from backend membership.
While the Ready log covers the initial image, the sender uses that configuration
and the log term at the image index. Installing a replacement backend clears
the cached configuration. The fallback reads the frozen metadata and can
rebuild the configuration from the membership in the streaming transaction.

The apply worker tracks its own cursor from the startup snapshot through
each serialized job. This matters on restart, when the backend's applied
index can already exceed the worker's position. Local snapshot creation
attaches a lower bound for this incarnation's worker cursor. The server
can therefore establish the physical index comparison immediately after
the term matches, including in the replay window.

The Go regression reopens a database at index 7 with a recovered HardState
commit of 3 and verifies the sent snapshot for both formats. The Lean
proof now reads the index and term from the very transaction that the
reader streams. The apply thread can now open the snapshot with its actual backend
index even while the cursor is behind. Lean also follows the schema reader
to its nil return on a pre-3.5 image missing the ConfState key, preserving
the same snapshot for streaming. The remaining proof must connect the
configuration and the legacy term to the committed prefix, including
after a power loss.
[Replay issue and regression](../issues/etcd-merged-snapshot-replay-failure.md).

### Replay proof handoff, November 21

At fork revision `1e59f9f173ea` the VM checked the sender with cached and
uncached configuration, the range check on the immutable log, and the
clearing of the cache on snapshot install. The Go regression covers both
paths for each disk format. The ordinary apply job still needs a proof
that the Ready log covers the durable index and supplies its entry term.
The ordinary apply proof now constructs the merged message, bundles the frozen
database with the Raft evidence, and sends it when its Ready supplies that term
history. The checked run loop transports the evidence from the apply channel.
The remaining producer is the Raft worker.
The earlier checkpoints below record which parts were checked independently.

The public Grove pin removes the index comparison at `7bc6d14671`; the
replay report and its failing test are on `lean` at `044d40223c`.
The replay fork still needs its own successful server build and gates.
The VM checked `ApplyAllSnap` in both auth modes after pulling public
`lean` at `2ca9ce4d1d`. Installing an incoming snapshot puts the backend
at the apply cursor, so a same-term request can use the caught-up sender
proof with the job's replay field. The ordinary entries branch
now reaches the sender with a backend ahead of that cursor. The physical
snapshot borrows the buckets of the durable log while keeping the replayed
in-memory membership. The VM checked this window and both merged server
constructors at public `lean` revision `a9b495f0e9`. The ahead branch still
has to certify the outgoing metadata. The VM checked the full five-argument
sender through message construction for both formats. Its caller must identify
what the real configuration decoder reads from this image and supply the
durable term or the legacy Ready lookup. The present-key schema proof opens
the frozen row, calls the decoder on its bytes, and returns the snapshot
share. These checks do not yet establish the value-specific codec facts.
The VM checked the constructor that carries the initial replay-term slice
into `raftNodeConfig`. It also checked that cutting an overwritten term
range or joining adjacent equal-term ranges preserves earlier lookups.
The VM checked `replayTerms_prefix` for the full slice expression
`r[:n:n]`. It retains the readable prefix and gives the writer zero
spare capacity, so the next append cannot overwrite an earlier Ready.
It also checked the translated empty-entry return of `appendEntries` and
the bootstrap case for a nonempty batch with equal endpoint terms. From
a nil receiver the translated method returns one run with the actual
first and last indices and the first term. `replayBatch_ordered` derives
term ordering for sublists of a recorded full Raft log. This justifies
the endpoint shortcut when the input is tied to that log. Mixed terms
and updates to an existing history are still open.

The ordinary apply proof now carries the initial backend log from the server
constructor to the job. Its durable index is below a commit certified in the
message term. The worker can use either the current Ready or a receipt from
an earlier term that covers the image. The latter rule does not require the
recovered WAL commit to cover that index. The existing graceful restart
producer uses the current Ready. The VM checked both receipt paths, the run
loop's handoff, and the ordinary replay send continuation through delivery.
The remaining sender precondition needs the metadata of the frozen image.

Three obligations still need proofs.

1. At startup and at each Ready, connect the immutable ranges supplied to
   this apply job to Raft's log. The translated `raftNode.start` now reads
   and clears `initialReplayTerms` before its loop, then updates the ranges
   as it builds the job. The constructor proofs for fresh and restarted
   servers now give the worker exclusive ownership of the config field.
   The VM checked both constructors and their Raft installer. The worker
   proof reaches the new `appendEntries` call on both snapshot branches.
   On the receiving side, both job constructors in `EtcdServer.run` now
   pass the concrete `toApply.replayTerms` header to `applyAll` from the
   heap-allocated job. The VM checked `EtcdServer__run` on this change.
   Giving the worker the field establishes ownership of the slice header.
   The historical runs in its backing array still need a log certificate.
2. Read the configuration from the frozen image. The missing-key branch
   of `schema.UnsafeConfStateFromBackend` is checked, including returning
   the snapshot share to the streaming reader. The present-key branch
   decodes a `raftpb.ConfState`; the legacy fallback decodes a
   `*membership.Member`. The current `json.Unmarshal` contract only covers
   `membership.ConfigChangeContext`. The existing ConfState writer contract
   bounds the serialized length; it does not identify the serialized
   configuration. The installed format and each read must agree.
   The VM checked the translated legacy `confStateFromMembers` loop. Every saved
   map key occurs exactly once in its enumeration. Both returned ID slices use that
   enumeration, partitioned by each member's stored learner bit.
3. Retain the historical quorum certificate for the durable backend index.
   `committedAtTerm_mono_term` transports that certificate to a later
   term. The existing graceful-restart contract takes `i ≤ σ.commit`;
   the disk state in the regression has `i = 7` and `σ.commit = 3`.
   The proof has to connect the actual persisted history and the leader
   term without this inequality.

## The two MemoryStorage writers and the apply job

Bootstrap now allocates the saved node location before starting Raft and
fills it with the actual node afterwards. A restart tags its initial image
at the WAL base. The driver attaches the receipt for the installed index
to `ApplySnapshot`. The apply thread attaches its applied-index lower
bound to `CreateSnapshot`. Compaction preserves the same storage invariant.

The apply job uses the outgoing channel from the node that produced its
Ready. The run loop supplies the exact delivered length of that Ready
and the boot snapshot bound. The successful merge can compare the index
against its applied-index authority after the first Go step, including
when the outbox and apply job refer to different Ready batches.


## Server proof at the two channels

Raft’s outgoing Ready observation now travels with the specific message in
`msgSnapC`. The apply job receives the observation from its own Ready in
`rnRtOk`, and the driver gets the installation receipt for a snapshot Ready.
`srv_snapshot_index_le` compares both observations at the original send term.
It covers the restored-log case and all three ways the server can fill memory
storage. The stored-source case uses the tag from that attachment, the
apply thread’s applied-index authority and the receipt for the local node.

The concrete boot and restart wrapper returns its Raft tag pin. Its callers
still select the ordinary validity predicate. The remaining integration must
select the server tag when attaching memory storage, furnish it in both
writers, and tie the node and delivered prefix to the apply job. The Go
index check and replay-window failure are both still in the pin.


## Snapshot installation receipts for memory storage

A Ready carrying a snapshot yields `nodeInstalledIndex` for this node
incarnation and the installed index. The driver can put that receipt in
the snapshot's storage tag. `readySnapSources_installed_le` uses it after
a snapshot is read back from storage. Each new restore exceeds the node's
previous commit, so a receipt at an already queued index identifies a
restore in the queueing node's history. This supplies the original sending
term even when the queue waits across elections.

On the server side the three tag sources are the boot index, the apply
thread's applied-index lower bound at creation, and this installation
receipt. The server's tag must refer to the same node attachment. The
MemoryStorage tag and the queue and apply-batch resources still need to
be retained in the server proof.

## Original send term across Ready batches

The raw node records each queued snapshot's committed index and the term at
which it was stamped. A successful restore answers with an append response
and requires an index above the old commit. It therefore cannot create a
new restore at the index of an already queued snapshot. Elections, ticks,
configuration changes and Advance preserve this fact. At handout the proof
matches the concrete message to its member of the protocol outbox.

`readySnapSources_le` compares the restored snapshot with the applying
Ready in the message's own term, even if its sending Ready drained the
message in a later term. The storage case still returns the caller's storage
tag. For the server, creation and bootstrap can supply the applied-index
lower bound. Installation from a snapshot Ready needs that Ready's restore
evidence and its position in the driver's batch sequence.

## 2026-11-20 · the Ready history and the remaining send-time obligation

The main linked proof passes with a monotone restore history on each RawNode.
Every log restore raises the boundary past the old committed index. A Ready
with a snapshot hands out the committed log ending at that boundary. Without
a snapshot the boundary is at or below the apply cursor. These two cases bound
all restored indices by the length of the log handed out in this Ready.

The Ready channel carries a persistent observation at the hard-state term that
the receiver enters. `readySnapSources_sameTerm_le` compares two Ready batches
from the same node incarnation and term. In the storage case it returns the
application’s storage tag. In the restore case it uses the foreign leader’s
message and election safety to bound the index by the observed batch.

An outgoing message can stay queued across a term change. Its own stamped term
can then precede its handout’s hard-state term. The server’s term check uses the
message term, so the same-term result alone cannot discharge the server proof.
The remaining Raft obligation is to retain the receive term through
`raftLog.snapshot`, `maybeSendSnapshot` and `raft.send` for this case.


## Term and index comparison (2026-11-20)

The node now has a ghost name for a history of term and index observations.
The send-time lemma bounds the restore term by the term in which the node
stamps the outgoing message. Election safety excludes equality when the
incoming snapshot came from another member. A Ready observation in the
outgoing term therefore bounds the restored index (`restoredSend_index_le`).

The comparison is checked under explicit hypotheses. The remaining work is to
carry the history authority through each live RawNode, issue observations at
the physical send and Ready, and relate the Ready index to the server’s apply
cursor. The runtime guard is still in the etcd pin.

## Storage contract progress (2026-11-20)

The main raft build checks `isStorageP_mono_SV`, the tagged storage contract
`isStorageT`, the tagged memory-storage invariant, its allocation
`memStorInvT_alloc`, and its contract law `memStorage_isStorageT`. Existing
clients can keep their original validity predicate. Both startup functions now accept any persistent storage certificate that entails
`snapshotValid` and return its `nodeTagPin`. Existing clients instantiate the
certificate with `snapshotValid`. The Ready receive now exposes `readySnapSources` at the node object for the
handed-out messages. Applying `readySnapSources_msgSnap` to one of them and the
startup pin gives either the client's storage certificate (under a later) or
the restore-path certificate. R2 still has to establish the term and position
of that restore in the node's history.

## Snapshot sender evidence (2026-11-20)

`sentMsg_localSnapshotLeader` identifies the node that sent a queued snapshot
as an elected leader in the message term. Its proof gets the id from the
outbox invariant and the election certificate from the protocol message.
`snapshotLeader_terms_ne` rules out equal terms for two distinct leaders.
The remaining comparison needs the term of the *local restore* and the
position of the Ready batch in the apply thread.

## Incoming snapshot source at Ready (2026-11-20)

Both Step paths retain the protocol message on a successful restore. Its
snapshot index and log term match the pending snapshot, and its sender differs
from the receiver. The Ready contract carries this evidence to the server via
`nodeRestoreSource`. The next obligation is to order the restore relative to
the Ready batches already applied when the server consumes the outgoing message.

## Queued snapshot provenance (2026-11-20)

The unstable branch of `raftLog.snapshot` returns a snapshot in the node's
`LogState.ksn`. The outgoing message now carries that membership from
`raft.maybeSendSnapshot` through both message queues to
`RawNode.readyWithoutAccept`. The storage branch retains the storage
certificate supplied at startup. A successful restore appends to `ksn`, so
later log updates preserve the queued evidence.

The remaining step is to associate each member of that list with its
successful incoming Step and to compare its term and index to the Ready
already processed by the server.

## Outgoing restore evidence at Ready (2026-11-20)

`readySnapSources_msgSnap` now returns the sending node's local restore source
alongside its restore certificate. `SnapLogStep` appends the actual incoming
snapshot on both successful Step paths. The local history survives handling
further messages, acknowledgments, and draining the pending snapshot. Restart
and Bootstrap start a fresh history. The remaining temporal comparison must
bind the incoming protocol message's term to the local restore and order it
against the Ready processed by the apply thread.

## HANDOFF (2026-11-20, first session paused by the coordinator)

**Done** (branch `prove-nosnapguard/2026-11-20`, worktree `/shared/etcd-grove-wt/prove-nosnapguard`, off
`lean` ed714ac34e; notes only, no Lean or fork change, nothing landed or pushed): b1adece81f (plan, (I)
argued true), d92dbc16a8 (refined design: the raft registry; replay-window analysis), and this handoff.
A baseline VM build of the clean branch was started (`/shared/tmp/nosnapguard/build0.log`, `rc=` at its
end). Fork checkout at d3feef9bc: `/shared/tmp/nosnapguard/etcd`; raft d2c16c558: `/shared/tmp/nosnapguard/raft`.
The user approved the raft API / storage-contract change (2026-11-20) and wants the replay-window
deferral (6e8f0c004) fixed properly afterwards (no drop/defer/report-failure as a resolution).

**Exact next step: stage 1 (R1), found plumbing.** The source distinction already exists inside raft:
`tsSrc sn ty snap` (`InvRaftPhys.lean:1015`) = `svCert sn sv` (storage-sourced, the pin `sn.gsv` of the
contract's `SV`) `∨ ksnCert sn …` (received/restored); the outbox carries it as `qSrcs` (`ownRaftPhys`'s
`Hscert`), and a `Ready` converts it to `qCerts` (`RawNode__readyWithoutAccept.lean:159`,
`RawNode__acceptReady.lean:272`), losing the source. So R1 needs **no new pin**: put the client tag in the
pinned `SV`.
1. `InvStorage.lean`: lemma `isStorageP_mono_SV` (SV occurs only in `HSnapshot`'s post).
2. `InvNodeRule.lean:775`: `isStorageT γ K Tg st := isStorageP … (fun sv => snapshotValid γ sv ∗ Tg sv) …`;
   `isStorage := isStorageT … (fun _ => True)` (clients that build `isStorage` from `isStorageP` at
   `snapshotValid` go through the mono lemma: `MemstorageApi.memStorage_isStorage`, kv `KVStorageInstance`,
   kvreconf `KvrStorageApi`, kvdurable `KdStorageApi`, `TracedApiDraft`).
3. `RestartNode.lean`/`TracedStartNode.lean` (and `Spec/.../RestartNode.lean`, `StartNode.lean`): take
   `isStorageT … Tg`, allocate the `gsv` pin at `snapshotValid γ ∗ Tg` (line ~546 / ~431), generalize
   `certLink_make` (line ~200 / ~220: take the left conjunct after `saved_pred_agree`), and give the client a
   persistent `nodeTagPin γ n Tg` (`∃ γn, nodeTabOk γ n γn ∗ savedPredOwn γn.sn.gsv (snapshotValid γ ∗ Tg)`;
   `cfgNamesOf` already includes `sn.gsv`, `sn.gk`).
4. Ready slot: follow the path of restart S7.3's `snapToOk` slot exactly (`LemmasReadyR.lean:305`,
   `InvRawnodeReady.lean:1533/2254/2481/2880`, `RawNode__readyWithoutAccept.lean:623`,
   `InvNodeChan.lean:902`, `InvApi.lean:2164/2859`, `InvNode.lean:834` `readyRest`,
   `TracedRawNodeReady.lean:65`), adding `[∗list] q ∈ ms, qSrc s.gh.sn q` (persistent, from `Hscert`)
   and at the API `snapSrcN γ n st` (`∃ γn, nodeTabOk γ n γn ∗ tsSrc γn.sn …`); `readyRest` needs the node
   `n` or an existential over `γn` tied to it. Law: `snapSrcN γ n st ∗ nodeTagPin γ n Tg ⊢ ⌜ty ≠ MsgSnap⌝ ∨
   ∃ sv, ⌜snap = some sv⌝ ∗ (▷ Tg sv ∨ nodeSnapRecv γ n sv)` (`nodeSnapRecv` opaque, enriched in stage 2).
   Clients destructuring `readyRest` (kvreconf/kvdurable `Replica__run`, server `InvRaftNode`) update patterns.
5. `MemstorageApi.lean`: `memStorJT γ K Tg` (SV := `snapshotValid γ ∗ Tg`), `memStorInvT`,
   `memStorage_isStorageT`; keep `memStorJ`/`memStorInv` as they are (the `True` instance) so other
   clients are untouched. The memstorage method specs need no change (`J.SV` already guards
   `ApplySnapshot`/`CreateSnapshot`/`Snapshot`).
6. Regenerate `interface/` (`etc/gen-interface.py etc/api/raft.txt`, after the build), `etc/gen-raft-tla.py`
   (RaftTla copies) and the RaftNoAx copies by their script; `etc/tcb-report.py --check` unchanged; supersede
   `notes/decisions.md` "The merged snapshot's index guard" (the user's 2026-11-20 instruction supersedes the
   2026-10-31 deferral of (A)/(D)) when landing stage 1.

**Gotchas.** `memStorInv_alloc` (`MemstorageApi.lean`) is a `sorry` (PORT, durability stage II): do not
add a second one, prove `memStorInvT_alloc` from `memStorInvP_alloc` or reuse whatever the server's
attach really uses. `StorNames`/`MemStorNames` are stored as tuples in ghost maps (`storKeyNames`,
`cfgNamesOf`, `MemStorNamesRec`): adding fields there is costly, which is why the plan avoids it. Stage 2's
registry is the hard part (time ordering; see "Refined design"). All Lean runs on the VM
(`/shared/tmp/vm-build.sh`, `VM_CMD=...`); land with `ETCD_GROVE_GATES=/shared/tmp/vm-gates.sh etc/land.sh`.

**Open question (replay-window fix, after the guard removal).** Labelling the in-window merged snapshot with
the backend's own `(ci, term at ci, conf state at ci)` is right when `ci ≤` the sender's committed index
(graceful restarts). After a power loss `ci` can exceed the WAL's (hence raft's) commit index
(`nonissues/etcd-backward-snapshot-install-panics-watcher.md`, crash path): what should the merge send
then? Its label must be an index raft has committed (`isMessage_snap_recontent` needs a `commitWit` of
`m.Term` with `c ≥` the label), but the backend's content is at `ci`; no deferral is acceptable.

Goal (the user's): delete `&& m.GetSnapshot().GetMetadata().GetIndex() <= ep.appliedi` from
`applyAll`'s `msgSnapC` branch (fork commit 633036387, `goose-lean-snapguard`; `notes/decisions.md`,
"The merged snapshot's index guard") by proving what it stands in for:

> **(I)** a `MsgSnap` `m` that `applyAll` of batch `i` reads from `msgSnapC` with
> `m.Term == apply.raftTerm` has `m.Snapshot.Metadata.Index <= ep.appliedi` (after batch `i`'s
> snapshot and entries are applied).

The guard is not acceptable as a resolution (the user, 2026-11-20): dropping the message and reporting
a failed snapshot turns an unproven safety obligation into a liveness hole. The replay-window
deferral of 6e8f0c004 (`ep.appliedi < ConsistentIndex()`) stays; it is a different question (below).

## (I) holds: the argument, against the fork's code at d3feef9bc and raft d2c16c558

Notation: Ready `k` is the `k`-th `Ready` the raft goroutine (`raftNode.start`) takes; it sends batch
`k` to `applyc` before it processes Ready `k`'s messages, so a `MsgSnap` of Ready `j` enters
`msgSnapC` after batch `j` is queued. The apply thread runs the batches in order (FIFO scheduler), and
may lag: batch `i < j` may read Ready `j`'s message. `raftTerm_k` is the term of the last non-empty
`HardState` of Readys `<= k`. `apl` is `ep.appliedi`: monotone (`applySnapshot` panics on a snapshot
not past it; entries move it forward), at boot the storage snapshot's index (`server.go:808`), and after
batch `k` at least every snapshot of Readys `<= k` (`applySnapshot` sets it, line 1183).

`m` (term `T = raftTerm_i`, in Ready `j`) carries `raftLog.snapshot()` (`log.go:293`), read when the
leader of `T` generated it:

1. **the unstable snapshot** `S`, restored (`raft.restore`, only in `StateFollower`, from a `MsgSnap`
   of the leader of the follower's term `T_r`) and not yet stable. `S` is in the first Ready computed
   after the restore, `h`. If `h <= i`, batch `i` applied it. If `h > i`, Ready `i` was computed before
   the restore, so `T = raftTerm_i <= T_r`, and `m` (generated after the restore, at term `T`) has
   `T >= T_r`: `T = T_r`, and the node would be leader of a term in which it followed another leader
   (election safety: impossible).
2. **the storage snapshot**, put there by
   - `CreateSnapshot(ep.appliedi, …)` (the apply thread, `server.go:2143`): at most `apl` then, so at
     most `apl` now; or the boot snapshot (`bootstrap.go:744`): at most the initial `apl`;
   - `ApplySnapshot(raftSnap)` of Ready `h`'s snapshot (the raft goroutine, `raft.go:287`), before
     `m` was generated: as in 1 with that `h`.

So **(I) is true**: no counterexample, nothing for `issues/`. The term check is what makes it true
(without it, case 1/2 with `T > T_r` is a real stale merge: `issues/etcd-merged-snapshot-stale-term.md`).

## What a proof needs (none of it exists today)

Today `rnSnapMsg` (`InvRaftNode.lean`) knows nothing of `m`'s snapshot index (`SentMsgShape`: `< 2^61`);
raft's storage contract bounds the stored snapshot only by the node's commit (`DL = nodeCommitLb`),
which may be past `apl` (the apply thread lags). Three pieces:

- **R1 (raft API: the snapshot's source).** For each `MsgSnap` a `Ready` hands out (in `msgOut` /
  `sentMsg`'s companion, or a new persistent `snapMsgSrc` beside `rnSnapMsg`'s `sentMsg`): its snapshot
  is either one `Storage.Snapshot()` returned (a client-chosen persistent tag, a new field of the
  storage contract's `Snapshot` post, default `True` for the clients that do not care), or the
  unstable snapshot restored at a term `T_r`, handed out in a `Ready` no later than this one, with
  a token `restoredAt T_r`. Raft internals: `raftLog.snapshot`'s spec (two cases already, U8 v2) to
  carry the tag / `ksn`'s restore term into `maybeSendSnapshot`'s message ghost.
- **R2 (raft API: terms).** `restoredAt T_r` is exclusive with "this node sent a `MsgSnap` of term
  `T_r`" (election safety: the restore's sender was `T_r`'s leader, `isMessage .snap`'s sender log of
  `T`'s leader), and a snapshot `Ready`'s `restoredAt T_r` has `T_r >=` every earlier `Ready`'s
  hard-state term (the driver's `hardState`, monotone).
- **R3 (server).** The storage tag for `srvStor`'s `MemoryStorage`: `CreateSnapshot` by the apply
  thread tags with `apl`'s monotone lower bound (`ep.appliedi`'s authority, the apply thread's);
  `ApplySnapshot` by the raft goroutine tags with "Ready `h`'s snapshot" (the batch index `h` in the
  `sspscConsumer γ.ap` list); boot with the initial `apl`. `rnSnapMsg` gets the Ready index `j` and R1's
  source; batches record `(raftTerm_k, snapshot index_k)` (already in the `toApply` list). At the merge
  in batch `i`: case `j <= i` or `h <= i`, `apl >=` that snapshot; otherwise R2 refutes `T = raftTerm_i`.
  Then `srv_merged_sent`'s `hle` comes from (I) instead of the guard, and the fork drops the clause.

Size: R1/R2 change raft's exported API (`etc/api/raft.txt`'s interfaces, the storage contract every
raft client instantiates, `RaftTla`'s generated copies) and raft's send path proofs; R3 changes
`InvRaftNode`/`InvRaftLoop`/`InvApplyAll`, the raft goroutine's proof (`raftNode.start`) and
`applyAll`. Estimated several sessions; it was option (D) of the 2026-10-31 decision ("term-tagged ghost
state across the raft loop, the storage and the apply thread"), plus (A) (a raft API law on where a
`MsgSnap`'s snapshot comes from). The user approved the API change on 2026-11-20. See the completed stages above.

Not an alternative: weakening `sentMsg_replaceSnapshot`'s premise to the leader log's base of `T`
(`isMessage_snap_recontent` uses `m.index <= ai` only to put `ai` above that base): bounding that base
by `apl` needs the same term and ordering reasoning (the base moves by the same restores and
compactions).

## The replay-window deferral (6e8f0c004): same flavour, but bounded (to be fixed too: the user, 2026-11-20)

Inside `ep.appliedi < ConsistentIndex()` the merge is skipped and the snapshot reported failed. The
window closes: after a restart raft re-delivers the committed entries from the storage snapshot up to
at least the backend's consistent index (they are in the WAL: the consistent index was applied from
them), so the apply thread passes `ConsistentIndex()` and later `MsgSnap`s are merged. The leader
retries after `ReportSnapshot(…, SnapshotFailure)` (the follower's progress goes to `StateProbe`, then a
new `MsgSnap`), so this is a delay, not a permanent liveness hole. The proper fix is to send what the
backend holds: merge at the backend's own index, i.e. label the merged snapshot with
`ConsistentIndex()`, its term (`ConsistentApplyingTerm`/the backend's term key) and the conf state at
that index, instead of `(appliedt, appliedi, ep.confState)`; then nothing is deferred. Not done here.

Analysis for the fix (2026-11-20, not started). Inside the window the backend is at the consistent index
`ci > appliedi`, so the only correct label for the whole backend is `ci`'s: index `ci`, the term the
backend stores with it (`schema.UnsafeReadConsistentIndex`'s term), and the conf state the backend stores
(`schema.UnsafeConfStateFromBackend`), read in the same read transaction as the backend snapshot that is
streamed. Outside the window `ci = appliedi` and the label is today's. Constraints to check before
choosing it: (a) `ci` must be committed and in the sender's raft log at a term the merge lemma accepts
(`isMessage_snap_recontent` needs a `commitWit` of `m.Term` with `c ≥ ci`): true after a graceful
restart (`ci ≤` the saved commit), false after a power loss (`nonissues/etcd-backward-snapshot-install-
panics-watcher.md`'s crash path: `ci` can exceed the WAL's commit), where the label would claim an index
the sender's raft has not committed; (b) the proof needs the backend's image at `ci` (`srvImage` of the
log through `ci`), which the restart proofs (`srvWinPend`) already reason about for the window. So: with
(a), label at `ci` when `ci ≤` the batch's committed bound, and otherwise (crash case only) the open
question is what upstream intends; record it then.
