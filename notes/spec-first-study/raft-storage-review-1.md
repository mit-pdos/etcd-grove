# Review 1 of candidate 16 (raft's storage as an ordinary object, linked by raft's invariant)

Reviewed at `raft-unified` 63ad16cafa (worktree `raft-spec-review`), against raft at
`.lake/go-src/raft` and etcd at `.lake/go-src/etcd`. As the coordinator asked mid-review, §1
(MemoryStorage's own table) was not checked against `storage.go`. This review covers §2-§4 and §7.

## Verdict

The direction is right, and most of it can be proved. Raft gives up owning the storage. The
certificate registry (`storCert`/`storageCertLink`, 16 files) goes. So do the hold, the terms and
the lent storage. `storSnapLb` replaces what the server builds for itself today (`memTokShared` plus
a mono-nat in `srvStorTokN`, `InvApplyAll.lean:123-164`).

Two findings are blocking:

- **A1**: the compaction law is unsound. It allows compacting past raft's `applied`, which is the
  known etcd panic.
- **A2**: no client can learn the storage's snapshot exactly. kvreconf and etcd's `run` both need
  that.

There are also three statement-level errors and two simplifications.

## What is good

- **Raft never reads the storage while a snapshot is pending.** That makes the snapshot window of
  the link easy to state. `firstIndex`, `lastIndex`, `term`, `slice` and `snapshot` all answer from
  `unstable` once `unstable.snapshot != nil` (`log.go:293-320, 387-413, 499-505`). The link can be
  loose in that window, with no lending needed.
- **`storCovers` is monotone (open point 2: yes).**
  - A batch starts above `committed`: `raftLog.append` panics on `after < committed`
    (`log.go:137-139`), and `maybeAppend` panics on `ci <= committed` (`log.go:119-120`).
  - Otherwise a batch continues from `offsetInProgress`, past everything handed out before.
  - In synchronous mode only one `Ready` is outstanding (`rawnode.go:411-413`).
  - A restored snapshot is above `committed` (`raft.restore`), so `ApplySnapshot` keeps every
    covered prefix below its index.
  - This needs the existing `AsyncStorageWrites = false` premise. State that in `storCovers`'
    docstring.
- **`appendReceipt_covers` is the right answer to H1 of review 9.** It gives the mid-`Ready`
  witness without a hold: delivered entries are stable or in this `Ready`'s batch.
- **`storLink_createSnapshot` asks for no term.** That answers the user's `storTermsAt` point.
- **The certificate argument is right.** "Compacted ⇒ a certified snapshot at or past the boundary"
  (`offset ≤ snap.Index`, the cert in the invariant) is exactly what `maybeSendSnapshot` needs
  (`issues/raft-compact-past-snapshot.md`).
- **Two writers (open point 5) are fine.** The laws rest on a persistent link, so etcd's raft
  goroutine and apply goroutine can each use them.
  - etcd sends `notifyc` before its `ApplySnapshot` (`raft.go:272-277`). The apply goroutine's
    `CreateSnapshot`/`Compact` can therefore race it.
  - Both orders end in an answered error (`server.go:2106-2108, 2154-2156`), which the laws'
    error outcomes cover.
  - The WAL is not the storage's concern.

## Findings

### Tier A (blocking)

**A1. Compaction past raft's `applied` (hard rule: sound).**

- *Evidence.* `storLink_compact` takes `storCovers l` with `x ≤ |l|`. `appendReceipt_covers` hands
  out `storCovers st.delivered` in the middle of a `Ready` (spec §4, lines 138-140, 157-159), and
  the invariant only bounds `offset σ ≤ |delivered|` (line 119).
  - Raft reads from `applied + 1`, not from `applying + 1`: `hasUnappliedConfChanges` scans
    `[applied+1, committed+1)` and `Panicf`s on `ErrCompacted` (`raft.go:995-1019`, through
    `mustCheckOutOfBounds`, `log.go:551-557`).
  - `applied` moves only at `Advance` (`log.go:332-345`).
  - So a client that compacts in the middle of a `Ready`, up to delivered > applied, makes a campaign
    in that window panic. That is `issues/etcd-compact-past-raft-applied.md` exactly.
  - Today's floor exists for this. It is raised at the `advancec` rendezvous, and the reads from
    `applied+1` take `fl ≤ applied` outside that window (`InvRaftlog.lean:650-663`, `FlOk`;
    `RNState.flw`).
- *Callers affected.* None of them needs the unsound case:
  - kvreconf compacts only after `Advance` (`kv.go:372-378`).
  - etcd with the fork's fix compacts only after `raftAdvancedC`.
  - So the restatement costs no client anything.
- *Restatement.* Keep two witnesses, separated by where they come from:
  - `storCovers γ N id l`, from the receipt or from `Advance`. It is the right to snapshot.
  - `nodeAppliedLb γ N id k`, persistent and monotone, given only by `Advance`'s post with
    `k = st.delivered.length`. This is the user's "track how much is applied".
  - `storLink_compact` then takes `storSnapLb γ N id x ∗ nodeAppliedLb γ N id k ∗ ⌜x ≤ k⌝`, with
    no `storCovers`.
  - The invariant's bound becomes `offset σ ≤ applied`, or, in the advance window, `≤ applying`
    with raft only running `rn.Advance`. That is today's `flw` argument, moved.

**A2. No client knows the storage's snapshot (hard rule: complete; open point 3: the reads must
say more).**

- *Evidence.*
  - kvreconf panics on any `CreateSnapshot` error (`kv.go:397-399`). Its own `index > snapIndex`
    test proves the panic away only if it knows the storage's snapshot index exactly. The candidate
    gives only lower bounds (`storSnapLb`). The `else` branch of `storLink_createSnapshot`'s COMM
    can never be refuted.
  - etcd's `run` reads `raftStorage.Snapshot()` before its loop starts (`server.go:754`). Its
    proof needs the answer to be the fresh, empty snapshot (`InvBoot.lean:462-467`,
    `rnSnapOnce_of_tok`, today from the client's `memSnapTok`). `storLink_read` gives nothing.
  - Frozen §4 kept the client's snapshot token for exactly this reason
    (`raft-node-unified-candidate.md:312-316`: "a client that is the storage's sole writer keeps
    the token and so knows the snapshot index").
- *Restatement.* The client is the storage's only snapshot writer, so give it the exact fact:
  - `storSnap γ N id (k, m, d)`: exclusive and timeless. The link keeps the other half.
    `StartNode`/`RestartNode` give it at σ0's snapshot.
  - `storSnap_lb : storSnap … ⊢ storSnapLb …`.
  - The two snapshot laws and `storLink_read` are atomic over it as well. Have the law take the
    client's `AU <{ ∃∃ s, storSnap γ N id s }> … <{ storSnap γ N id s', COMM Q }>` and return the
    storage method's AU.
  - Then kvreconf owns the token (AU trivial), and etcd keeps it in its own invariant (as it does
    `memSnapTokG` today). One law serves both, with no family.
  - This is a design choice the user should make (ghost state given to the client). The
    alternative is a Go change to kvreconf, tolerating `ErrSnapOutOfDate` as etcd does. That
    leaves etcd's `run` read still unproved.

### Tier B (must fix in the statement)

**B1. `RestartNode`'s `σ0 = MemState.withConf cs` excludes kvreconf's newcomers (hard rule:
complete).**

- *Evidence.* A newcomer's storage is a fresh `MemoryStorage`, whose snapshot has an empty
  `ConfState`. Its wrapper's `InitialState` answers `boot` (`kv.go:258-264`; `cluster.go:177-178`).
  So `σ0 ≠ withConf boot`.
- Today `RestartNode` keeps the two apart: the storage state is a premise, and a separate
  `InitialState` triple names the answer `(hs, csm)` (`interface/.../RestartNode.txt:34-58`).
- *Restatement.* Keep today's split:
  - `S σ0` with `σ0` the empty state (any `ConfState`).
  - A premise `{{ S σ0 }} st.InitialState() {{ hp cs, S σ0 ∗ hsOpt hp hs ∗ csPts cs □ csm al }}`.
  - `confStateIs csm γ.c0` on the answer.

**B2. `InitialState` cannot be one of `isStorageOver`'s atomic triples (hard rule: sound for the
instance; open point 4).**

- *Evidence.* `MemoryStorage.InitialState` takes no lock. It writes `callStats` and, through
  `EnsureConfState`, the conf state's `AutoLeave`, and it returns the storage's own pointers
  (`storage.go:128-134`; `issues/raft-memorystorage-initialstate-unlocked.md`). An atomic triple
  over the lock-protected `memState` cannot be proved for it. Today's spec takes the owner's
  `ownMemoryStorage` and the snapshot token together (`MemoryStorage__InitialState.lean`, D17d).
- Raft calls it once, in `newRaft`, before it allocates the link.
- *Restatement.* Drop `InitialState` from `isStorageOver`: it is B1's premise, non-atomic, on an
  `S σ0` the caller owns. `isStorageOver` covers the five methods raft reads while running.
- `Snapshot`'s temporary error does fit one family. Its result is "the clone of `σ.snap`, or
  `ErrSnapshotTemporarilyUnavailable`", with the state unchanged; kvreconf's coin
  (`kv.go:267-272`) commits at an unchanged state.
- State `Entries`' ownership in the triple: `entsRO`, `cap = len` and the prefix fact. `slice`'s
  `extend` relies on them (`InvStorage.lean:61-86`).

**B3. The laws' masks are reversed.**

- *Evidence.* The laws build an AU by opening the link, so its outer mask must contain `↑N`. They
  are written `@ ⊤ ∖ ↑N, ∅` (lines 134, 147, 159, 163, 169, 173), which excludes `N`.
- *Restatement.* Use `@ E, ∅` for every `E` with `↑N ⊆ E`, or the method's outer mask.
  - A mutex-based `MemoryStorage` needs no namespace. Its specs can take the AU at `⊤` (today's is
    `⊤ ∖ ↑memSnapN`, for the server's token invariant, which A2's restatement makes the client's).
  - `isStorageOver` should fix one mask, `⊤`, so that raft's link (and B3's `N`) open inside it.

**B4. The laws' COMMs must be functions of the method's result, and they must guarantee its
precondition.**

- *Evidence.* §1 states each method's AU as `<{ ∃∃ σ, memState σ ∗ ⌜pre σ⌝ }> … COMM Φ (result σ)`.
  - `storLink_createSnapshot`'s COMM mentions `σ.snap.Index` in its `else` branch. `Φ` sees only
    the result (`ErrSnapOutOfDate`), so the law cannot be fed to the method.
  - `storLink_compact`/`_createSnapshot`/`_applySnapshot` state `S σ` without `⌜pre σ⌝`, although
    the text argues that the panic is excluded. Only `storLink_append` states it.
- *Restatement.*
  - Each law's atomic precondition is `S σ ∗ ⌜pre σ⌝`.
  - `storLink_createSnapshot`'s COMM is
    `storSnapLb γ N id i ∗ (if σ.snap.Index < i then ownSnapsMade γ (Ss ++ [⟨|l|, m, d⟩]) else ownSnapsMade γ Ss)`.
    In the error branch the snapshot is at or past `i`, so `storSnapLb i` holds in both branches,
    and the made-set is decided by the error, which `Φ` sees.
  - etcd's path "`snapshot` returns on `ErrSnapOutOfDate`, then `compactRaftLog(appliedi)`"
    (`server.go:2102-2108, 1217-1218`) needs exactly `storSnapLb appliedi` in both branches.

**B5. A snapshot `Ready`'s append must come after its `ApplySnapshot`.**

- *Evidence.* With a snapshot outstanding and not yet applied, the `Ready`'s entries start at
  `s.Index + 1`, above the storage's `lastIndex + 1`. `Append` would panic ("missing log entry",
  `storage.go:321-323`), and if it did not, `ApplySnapshot` would then wipe the entries
  (`storage.go:235`). So `storLink_append` (whose AU promises `appendPre`) is false while a
  `snapRight` is outstanding.
- Today the order is enforced by the loan: `snapReceipt` requires `σr.ents = es`
  (`ApiVocab.lean:471-475`). etcd (`raft.go:277, 287`) and kvreconf (`kv.go:355, 362`) both apply
  the snapshot first.
- *Restatement.* For a snapshot `Ready`, `readySnap` gives `snapRight γ N id sv es`. The
  `storLink_applySnapshot` law returns `snapReceipt ∗ appendRight γ N id es`. `Advance` then takes
  `snapReceipt ∗ appendReceipt`, and the plain `Ready` gives `appendRight` directly. This is a case
  split on the `Ready`, not a family.

### Tier C (simplicity, minor)

- **C1.** Drop `storCovers γ N id []` and `storSnapLb γ N id 0` from the posts of `StartNode` and
  `RestartNode`. They are vacuous: make them laws, `storLink ⊢ storCovers []`, or omit them
  ("no conjunct whose reason you do not know").
- **C2.** Drop `storLink_read`'s `COMM ⌜σ.WF⌝`. A generic `S` cannot supply it unless `WF` is a
  field of `isStorageOver` or a fact of the invariant, and kvreconf's `maybeCompact` uses nothing of
  `FirstIndex`'s answer (`kv.go:409-423`: any answer is safe). With A2, the read is atomic over
  `storSnap` too, which serves etcd's `run`.
- **C3.** Keying the witnesses by `(γ, N, id)` is sound only if there is one link per id. That holds
  through `nodeFounder`/`nodeJoin`'s exclusivity, and kvreconf uses fresh ids (`cluster.go:175-176`).
  Say so in `storLink`'s docstring, or key them by a name the link allocates.
- **C4.** `storLink` taking `S` is fine. It is the object's own state predicate, not a meaning
  predicate, so "TaDa, not HoCAP" is not broken.

## Open points answered

1. **Provable at raft's reads with a batch outstanding:** yes. It is today's `PendLogOk`/`PendFrom`
   argument (`InvRaftlog.lean:576-590`) moved into the invariant: `σ.ents` is either raft's view or
   `storApp view batch`, and raft reads below the batch's first index. `LastIndex` is reached only
   with `unstable` empty, so with nothing outstanding (`log.go:311-320`). Compaction needs A1's
   bound.
   - **Recommendation:** prove `storLink … ⊢ isStorageWith (raftView γ id) …`, today's contract
     over raft's ghost fragment, as one lemma. The `raftLog__*` proofs then do not change.
2. Monotone: yes (above, "What is good").
3. The reads must say more: A2.
4. The temporary error fits one family; `InitialState` does not: B2, B1.
5. Two writers and the WAL: fine (above); see B4 for etcd's error path.

## Churn estimate

Counted over `Proof/go_etcd_io/raft/v3` and `Spec/go_etcd_io/raft/v3`, 776 files.

- **Mechanical.** The `[StorageModel GF]` section binder appears in 455 raft files (802
  occurrences), 3 server files, 9 example files and 468 `RaftWitness` files (its own copy). Dropping
  the class is a `sed` plus a regeneration of `interface/`, whose headers name it.
- **Semantic: 131 files name the storage vocabulary.** The vocabulary: `ownStorage`, `StorState`,
  `isStorage(With)`, `appendTok`/`appendedTok`, `storFloor`/`memFloorTok`/`fl`, the loan
  (`readySnap`/`snapReceipt`/`SnapLoan`/`readyOut`/`advReceipt`), `storCut`/`storCert`/`storCap`/
  `storTermsAt`, `storageCertLink` and `PendFrom`/`storAbsorb`.
  - 25 are `MemoryStorage` files, to be rewritten from scratch (simpler).
  - 30 are function proofs. With the derived-contract lemma of point 1, the reads (`raftLog__term`
    26 occurrences, `__slice` 14, `__snapshot` 13, `__firstIndex`/`__lastIndex` 11 each) stay
    almost unchanged.
  - Really rewritten: `RawNode__acceptReady` (18: the hand-out), `RawNode__Advance`,
    `node__Advance`, `node__run` (the floor raise becomes A1's applied witness), `RawNode__Bootstrap`,
    `StartNode`, `RestartNode` (allocating the link), and `raft__maybeSendAppend`/`raftLog__restore`
    (the cert).
  - 39 Spec files: mostly the 13 `MemoryStorage` ones, plus `NewRawNode`, `newRaft`,
    `newLogWithSize`, `setupNode`, `StartNode`, `RestartNode`, `node__Advance`.
  - 39 shared files. The heavy ones are `InvStorage`, `InvRaftlog` (`ownRaftLog`'s
    `HStorage`/`lentStor` become a ghost fragment), `InvApi`, `InvApiDyn`, `InvNode*`,
    `ApiVocab`, `InvRawnode*`, `SnapConf`/`MemCertLink` (go), and `MsgSnap*`/`StepR*` (the cert).
- **Total: about 130 files touched, of which about 20-25 are substantive rewrites.**
- **Clients.** The server touches 10 files (`SnapTake*`, `EtcdServer__compactRaftLog`, `InvBoot`,
  `InvApplyAll`'s `memTokShared`, which goes, `NodeApiLink`, `InvRaftNode`, …) and the examples 7.
- **The branch being replaced.** U8's `raft-unified-storage-wip` (+3123/−679 over 69 Proof/Spec
  files) is discarded rather than ported.

## Go bugs

None new. The findings rest on known issues:

- `etcd-compact-past-raft-applied` (A1)
- `raft-memorystorage-initialstate-unlocked` (B2)
- `raft-compact-past-snapshot`
- `raft-committedentries-stable-storage-doc`

## Revision priority within the candidate

1. §4 laws: A1, B3, B4, B5.
2. The client-side snapshot fact: A2 (goes to the user).
3. §3 `RestartNode`/`StartNode`: B1, C1.
4. §2 `isStorageOver`: B2, `Entries`' ownership.
5. §7: adopt the derived-contract lemma to keep the churn at the estimate above.
