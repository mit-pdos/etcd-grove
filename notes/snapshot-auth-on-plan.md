# Plan: the snapshot install with auth on (`applySnapshot` in mode `on`; spec-first)

**Status (2026-11-01): Draft, in Review** (branch `snap-auth-on-draft`, worktree
`/shared/etcd-grove-aon`, off `snap-j8a` `6683c4e982`). Scope's output below (Q1-Q4, with two
corrections of 2026-11-01 marked **Corrected**); the Draft is `etcdserver/SnapAuthOnDraft.lean`
(imported by nothing), section "The Draft" at the end; Q2's premise and the timing fix are the
user's after the Review.

## The target

`run`'s snapshot-payload job in mode `on` (`EtcdServer__run.lean:1413`, the auth-on twin of
SNAPSHOT-SORRY #8, `run.wp_proofOn` in the trust baseline). J8a (branch `snap-j8a`, in progress)
proves the mode-off job over `EtcdServer.applySnapshot.specSnap`, which assumes the mode off
(`hoff : E.authMode = .off`). The mode-on job needs a mode-on install spec, `specSnapOn` (or one
spec over the mode), and its proof. Independent of #7-on (the sender's mode-on image, after the
durability work): the receiver can be stated and proved over the image certificate's mode-on
definition, which the sender proves later.

## What Go does (fork `goose-lean`, `server/etcdserver/server.go:1020-1150`)

The same code in both modes: `OpenSnapshotBackend`, `ci.SetBackend`, `lessor.Recover`, `kv.Restore`,
`alarmStore.Recover`, then `authStore.Recover(schema.NewAuthBackend(lg, newbe))` (the store is never
nil), `cluster.SetBackend`, the old backend closed after the auth store moved (the fork's fix of
`issues/etcd-auth-snapshot-closed-backend-panic.md`). `authStore.Recover` reads the new backend's
auth state (enabled flag, revision, users and roles for the cache) and installs it: with auth on,
the member's auth state jumps from the state after its applied index to the state at the snapshot's
index, skipping every admin entry in between.

## What `specSnap` assumes that fails in mode `on`

| `specSnap` (mode off) | why it fails with auth on | the mode-on counterpart |
|---|---|---|
| `hoff : E.authMode = .off` | the point | `E.authMode = .on γa` |
| `hauthb`: the image's `auth`/`authUsers`/`authRoles` buckets are `authBoot`/empty | an image of an auth-enabled cluster holds users, roles, the flag and a revision | the buckets encode the auth state of the image's committed prefix: `(kvRaftOfOn … A').1` (`KVAuthModel.lean`), in S1's bucket encoding (`auth/Buckets.lean`) |
| `authRecoverOk ast` (`SnapRO.lean`: `Recover` in mode off, auth buckets at boot) | stated for the boot buckets only | `Recover` in mode on: `auth.authStore.Recover.spec` exists and is proved (S4) for any mode `M`; it needs the whole authority `authOwnF`, the new backend's read contract `authBackendOk be R M` and write contract `authWBackendOkR`, `permsFit`, `capNext` |
| `authApplyOk ast E.RD` (mode off) | | `authApplyOkM (.on γa)` exists (E2i) |
| the image certificate `srvImage` (in `snapDirInv`'s `img`, `snapRecv_image`): `dbImage` over `kvModel` | mode-off model | `dbImage` over `kvModelOn` and the auth buckets (the same definition #7-on (b) needs; the user's design: one image per cluster in the cluster's mode) |
| `srvSnapApplied`'s KV facts: `kvApplied A' x'` | mode-off KV ghost state | `kvAppliedOn γ γk st₀ A' x' st'` (`KVApplyOn.lean`) with `st'` the image's auth state |
| the apply thread's auth resource after the install | absent in mode off (`authApplyRes .off = True`) | `authApplyRes (.on γa)`: `authOwnFu`, `tieRes` at the new latest state, the write contract on the **new** backend (`authWBackendOk be' …`), `tpAdmin` |

## Design questions (for the user, one batch)

**Q1. The history's tie to the log does not survive a jump.** `authHistTie` (`KVAuthModel.lean`, H5)
keeps the store's history a *prefix* of `bootState :: admStates γr.kv st₀ A` for a committed `A`
(the cap's authority, `auth.capAuth`, raised by one admin entry at a time,
`authHistTie_raise`). After a jump from applied `A` to `A'`, `Recover` appends the image's state,
the last element of `admStates … A'`, skipping the admin states between `A` and `A'`: the history
is no longer a prefix. Options:
- (a) The tie becomes "a subsequence ending at the applied prefix's state" (the history's states are
  admin states of the committed log, in log order; the latest is the applied prefix's). The checks'
  verdicts only ever use "a recorded state" and "the latest state", so a subsequence suffices for
  them; the cost is restating `authHistTie`, `capAuth`/`capNext` and their users (the admin steps'
  `specT`, `tieRes`).
- (b) Keep the prefix tie; the install appends every skipped admin state before `Recover`'s (from the
  committed log, which the receiver has as `srvRLogLb A'`, `snapRecv_image`): a ghost-only catch-up,
  the history then a prefix again. Smaller change to the statements; the catch-up lemma walks
  `admStates` over `A'` minus `A` and needs the cap raised over each.
Recommended: (b), if the catch-up lemma goes through (it is ghost-only and local to the install);
else (a).

**Tried (2026-11-01, the user's "try the catch-up lemma"): (b) goes through, but not ghost-only.**
The latest state's ghost variable is tied to the `revision` atomic (`revCur`: `uint.nat r =
st.revision`), so the skipped states cannot be appended outside the atomic's store: the catch-up
happens in `Recover`'s `setRevision`, as a list append. Proved, in two Drafts imported by nothing
(no `axiom`, no `sorry`):
- `auth/CatchUpDraft.lean`: `authHist_appendL`, `authOwnF_revCur_appendL` (the list form of
  `authOwnF_revCur_append`), `authOwnF_revCur_appendN` (any list, empty included: then
  `authOwnF_revCur_keep`), `capAtM` (one cap lower bound at the whole new history), and
  `setRevision.specN` with its proof `wp_proofN` (today's proof with the list lemma; `spec` allows
  `opt.length ≤ 1`).
- `etcdserver/SnapAuthOnDraft.lean`: `authHistTie_catchup` (at a committed `A'` extending the applied
  `A`, the store's history is a prefix of `srvHist A'` and the cap is raised to it; both cases of the
  tie's log, behind or past `A'`) and `catchup_list` (the list to append, `(srvHist A').drop
  hs.length`, after which the history is `srvHist A'`, its last state `A'`'s).
Found on the way: today's `Recover` appends the read state unconditionally, which the tie forbids when
the state does not change (the cap's list has no state twice); the empty-list case covers it.
Left for (b): `Recover`'s mode-on variant appending the list through `setRevision.specN`, whose new
backend's read contract can then give the image's **known** state (a fact of the buckets), not a
recorded one: Q2's clause in that form.

**Q2. `Recover`'s read contract needs the new state recorded first.** `authBackendOk be R (.on γa)`
gives a read transaction whose state is `authSnap (.on γa) st`, i.e. already in the history
(`∃ i, authStateAt γa i st`). The new backend's state is the image's, which the member never
applied. ~~With Q1 (b) the catch-up records it before `Recover`.~~ **Corrected (2026-11-01, the Q2
survey):** with Q1 (b) as tried, the catch-up happens in `Recover`'s `setRevision`, and `Recover`
puts the new backend (with its `authBackendOk` in `beP`) under `beMu` at its `Unlock`
(`auth/authStore__Recover.lean:70`; Go `store.go:399-401`) **before** its own read (:84) and before
`setRevision` (:118): a concurrent `lockedReadTx` (`store.go:941`) can read the image's state `stI`
before it is recorded, so a read contract claiming a recorded state is false in that window (a
premise asserting it would be unsound). The order "catch-up, then the new backend's contract" does
not exist in the code; the Draft's two candidates (below) are the two ways around it.
Either way the new backend's `authBackendOk` in mode on is a premise of the install, from the
backend's read contract over the image's buckets (`authBeOn`/`authReadTxOk` at `on γa`). **Checked
(2026-11-01): nothing gives it for a later backend.** `auth.authBackendOk ab R (.on γa)` is a premise of
`auth_store_new_on` (`etcdserver/Results.lean`) for the boot backend only, from the server's
backend-contract premises (`authSchemaBoot`/`authSchemaSrv`, the schema's auth side over D22's
backend); `authApplyOkM` covers the write side on any backend, not the read contract. So the install
needs a new clause: the schema's auth backend over a later backend in mode on, its read transaction's
state recorded once the catch-up has recorded the image's. Since `authSchemaSrv` is a premise of
`NewServer.specM` and so of the exported mode-on results, **a trusted-statement change, for the
user** (as the blocker-1 row of 2026-10-27 was).

**Q3. The image's auth fact.** The mode-on image's certificate gives the committed prefix `A'` and
`[[], []] ++ R = kvModelOn … A'` (KV) and the auth buckets' decoded state `= (kvRaftOfOn … A').1`.
Where it is defined: (a) a mode-indexed `srvImage` now (`srvImage γ M i D`, the cluster's mode in
`SrvRaft` per #7-on (b)), with the mode-off instance today's text by `rfl`; or (b) a separate
`srvImageOn` for the Draft only, merged when #7-on is done. Recommended: (b) for the Draft (the
#7-on change waits on durability by the user's timing (c); a Draft can name it without moving the
network's payload), switched with #7-on.

**Q4. One spec or two.** `specSnapOn` beside `specSnap` (as `applyAll.spec`/`specOn` today), or one
`specSnap` over `E.authMode` now. The auth-mode merge's step 4 (`applyAll`, `run`, `start`, `Start`)
waits on #7/#8; the install spec is its callee. Recommended: `specSnapOn` beside it in the Draft
(J8a is still changing `specSnap`: merging now would conflict with it), merged in step 4.

## Dependencies and order

- **J8a** (`snap-j8a`, another session) is changing `specSnap` (the payload's `notifyc`, `srvSnapRm`,
  the transport's `R`s, the alarm store's model). The Draft of `specSnapOn` should be written over
  J8a's text once it lands, or over its branch head if the user prefers not to wait.
- **The Draft** (after Q1-Q4): `etcdserver/SnapAuthOnDraft.lean`, imported by nothing:
  `srvImageOn`, `authRecoverOkOn` (from `auth.authStore.Recover.spec` at `on γa`), the catch-up lemma
  (Q1 (b)), `specSnapOn`, and the glue to `run`'s mode-on job (what `rnApSnap` and `applyRes` give in
  mode on).
- **Not in this stage**: the sender's mode-on image (#7-on), the two shared holes
  (`mergedCreate_window`, `merged_image`), step 4's merged specs.

## Handoff (2026-11-01, etcd-grove-d0 → the session on `bootOk`/J8a)

The user handed the rest of this stage to the session working on `bootOk` (J8a). State:

- **Branch** `snap-auth-on` (worktree `/shared/etcd-grove-snapon`, off `lean` `f122faa440`): this note
  and two Drafts imported by nothing, no `axiom`, no `sorry` (`#print axioms` checked):
  `auth/CatchUpDraft.lean` (`authHist_appendL`, `authOwnF_revCur_appendL`/`appendN`, `capAtM`,
  `setRevision.specN` and `wp_proofN`) and `etcdserver/SnapAuthOnDraft.lean`
  (`authHistTie_catchup`, `catchup_list`). Not on `lean`; merge or cherry-pick it.
- **Settled: Q1 (b)**, the tie `authHistTie` kept as stated; the catch-up is a list append in
  `Recover`'s `setRevision` (not ghost-only: `revCur` ties the latest state to the `revision`
  atomic). Above, "Tried".
- **Open: Q2, the snapshot backend's auth read contract.** `Recover` reads the new backend before the
  catch-up records the image's state `stI`, so it needs a read contract giving exactly `stI`; after
  the catch-up, the store needs the existing mode-on contracts (`authBackendOk`, `authWBackendOkR`) on
  the new backend, as `authSchemaSrv` gives them at boot from `authLockI (.on γa) bootState`. Where
  the fact enters (the user's question, not decided):
  1. a trusted premise `authSchemaSnap` in J8a-4's form (at the open's creation step, over the image
     data `D`, carried in `bootOk` beside `#HmetaSnap`, taken by `specSnap`): changes
     `NewServer.spec`'s premises, so every exported mode-on result;
  2. a local trust-boundary axiom on schema's auth read side (`NewAuthBackend`, `ReadTx`,
     `UnsafeReadAuth*`): `NewServer.spec` unchanged, one more axiom;
  3. **proved** from schema's auth read side over the backend's verified `ReadTx` and the image's
     buckets: no new trusted fact, and `authSchemaSrv` at boot (a premise only because that code is
     not proved) possibly discharged too. My recommendation; first step a survey of which schema
     auth functions are translated or names-only and what `ReadTx`'s spec gives of bucket contents.
  Any of them needs a definition "the auth buckets hold `stI`". ~~(no bucket-to-`AuthState` decoding
  exists)~~ **Corrected (2026-11-01, the Q2 survey):** it exists, unused: `schema.authBucketsAre st D`
  (`etcdserver/InvAuthBackend.lean:143`, S1), with `userOutD_are`/`roleOutD_are` (given the
  encodings' injectivity as a hypothesis). Missing only the projection from a backend's buckets
  (`authDataOf`, in the Draft) and a boot form (the boot buckets are empty).
- **The survey's outcome on Q2** (2026-11-01, read-only,
  `scratchpad/authq2-survey.md` of the session): **option 3 is infeasible**, in both forms (the
  one-time read of `stI`, or discharging boot's `authSchemaSrv`): on the server's backend every
  bucket but `Key` is a hook bucket (`bridgeParams`, `mvcc/BackendBridge.lean:106`), and the
  readers' view (`vData`, `bView`, `rtHeld_view`) covers only non-hook buckets; the tracked-bucket
  token `rbOwn` follows the writer's contents, not the readers'. So a reader learns nothing of the
  auth buckets: proving the read contract needs a new backend mechanism (a readers' view of the
  tracked buckets, kept by every `Unlock`, commit and the read history): a restatement of the
  verified backend's core, 2.5-10k lines, plus a bbolt `ForEach` axiom and two encoding-injectivity
  facts anyway. Option 2 has option 1's content outside `NewServer.spec`'s visible premises. The
  survey's candidate: option 1 reshaped, **one generalized `authSchemaSrv`** covering boot and every
  snapshot backend, at the store's `R` (fixed at boot; `authSchemaSrv` picks one per backend), with
  a fix for the `beMu` window: (a) a persistent "announced" state `authSnap` accepts, (b) relax
  `revCur`, (c) Q1 (a)'s subsequence tie. The Draft drafts (a) and a variant of (b).
- **Then**: `Recover`'s mode-on variant over `setRevision.specN` and Q2's contract;
  `specSnapOn` (Q4: beside `specSnap`, merged in the auth-mode merge's step 4) over the mode-on image
  (Q3: a Draft `srvImageOn`, switched with #7-on after durability); `run`'s mode-on job
  (`EtcdServer__run.lean` ~:1413).

## The Draft (2026-11-01, branch `snap-auth-on-draft`)

All in `Proof/go_etcd_io/etcd/server/v3/etcdserver/SnapAuthOnDraft.lean` (imported by nothing; its
header lists the statements). Base: `snap-j8a` `6683c4e982` (J8a-5's 5e): `specSnapOn` is written
against that `specSnap` and `applyAll.specSnap`. Not rebased onto J8b (`snap-j8b`, which packages
the snapshot triples as conjuncts of the main specs: how `specSnapOn` is packaged is a question for
the user, Q4 below).

### Q2's timing: two candidates

The window: `Recover` publishes the new backend under `beMu` before it reads it and before
`setRevision`. Both candidates keep Q1 (b)'s prefix tie (`authHistTie`) and share the premise's
other parts (below).

**(ii) "Record first" (drafted in full; recommended).** The history is caught up **before**
`Recover`, ghost only: the skipped states and `stI` are appended to the history (both its
authority's three quarters and the revision invariant's quarter, the cap bound raised to the
committed log's history), while the latest state's ghost variable (`authCurHalf`, which `revCur`
ties to the `revision` atomic) stays at the applied state. No shared invariant ties the history's
last to the latest state: only the admin side's `authOwnF`/`authOwn` do, and the apply thread holds
the pending form `authOwnP hs N` instead. So `stI` is recorded before `beMu`'s window opens, and
every read contract, `authSnap`, and the verdict lemmas keep their text.
- `auth.authCatchUpFirst` (**proved**): `authInv ∗ authOwnF hs ∗ capLb (hs ++ N) ={E}=∗ authOwnP hs N ∗
  authLockI (.on γa) stI ∗ authStateAt (|hs ++ N| - 1) stI`. The lock's share at `stI` comes out, so
  the new backend's lock gets it at the premise's call, exactly as boot's lock gets the share at
  `bootState`.
- `setRevision.specP` (from `authOwnP` to `authOwn (hs ++ N)`, the atomic and the latest state moved
  to `stI`) and `Recover.specP` (reads `stI` through a new clause of the read contract, the latest
  state for a holder of the history's half, `authReadTxOkH`; post: the authority at `hs ++ N` with
  the flag and cache halves **tied to `stI`**, `authOwnT`, which today's `Recover.spec` does not give:
  its post has untied halves). `Recover.specP` takes no write contract (`Recover` writes nothing);
  today's spec takes one to rebuild `authWR`, the store's user attaches it instead.
- The premise's snapshot clause `authSchemaSnap γa R`: at a backend whose tracked auth buckets hold
  `st` (`authBucketsAt`), `st` **recorded** and the lock's share at `st` given: the read contract
  (`authBackendOkH`, implying `authBackendOk`) at the store's `R`, the write contract at the frozen
  hook and at every schema backend on it (`authWAtHook`), a write token `T` with its retirement, one
  `R` lent against the new backend's read token. **The same claim as boot's** (boot: `st =
  bootState`, empty buckets), so the trusted content is one fact at two kinds of backends.

**(i) "Announced" (drafted as definitions and specs; not recommended).** The catch-up stays in
`setRevision` (`setRevision.specN`); `stI` is announced by the cap's lower bound at the committed log's
history (`authHistTie_catchup`'s `capLb (srvHist A')`: no new ghost state). Costs:
- `authSnap (.on γa)` must be **redefined in place** to "a state of the cap" (`authSnapC`; recorded
  states are states of the cap, `authSnapC_of_snap`, proved), for every reader: `beP`'s contract is
  `authBackendOk` with `authSnap`, so `Recover.specC` is not even statable without it. Every verdict
  lemma that reads `authSnap` as `authStateAt` (VerdictLemmas, LatestTie, TieRes, CacheLemmas, Reads,
  ~60 uses in `auth/`) and authkv's read law (`authStateAt_setup`, which takes `authStateAt` from the
  verdicts) are restated over capped states.
- The admin side's latest clause is false in the window (the backend holds `stI`, `Recover` holds
  `authOwn hs` with `stI ∉ hs`): it must be guarded (`authReadTxOkC`: `stI ∉ hs → st = stI`), a
  backend-specific contract.
- The new lock gets the share only after `Recover`, so the premise gives the write token as a wand
  (`authLockI stI ==∗ T`).

### Q2's premise, common to both

- **The store's `R`** is fixed at the store's construction (`beP`, the readers' `authRd`), so the
  snapshot clause is produced **by the boot premise**, at the boot's `R`, and carried: the
  generalized premise `authSchemaSrvG` is today's `authSchemaSrv` whose post also gives the boot
  token's retirement and `authSchemaSnap γa R`; boot's `authSchemaSrv` is its weakening
  (`authSchemaSrv_of_G`, **proved**). `NewServer.specM true`'s premise list keeps its length; its
  text changes (the user's decision: a trusted statement).
- **The lock's share of the old backend** (a finding of the glue): `Recover` (any candidate) appends
  with the whole authority `authOwnF`, whose batch-lock quarter is in the old backend's batch lock,
  which the install never takes (Go's `applySnapshot` locks no auth batch transaction). So each
  backend's write token must give the share back when the backend is retired (`authLockRetire γa
  T`: `T ==∗ ∃ st, authLockI (.on γa) st`), a new clause of the premise (boot's token too).
- **`Recover`'s own read** needs one `R`: lent by the clause against the new backend's read token
  (`mvcc.bkRTx`, which the mode-off `authRecoverOk` takes), given back.
- For the axiom check (spec-first-plan's): "any `W`" at the new backend (as J8a-4's review found for
  `isMetaBackend`); `R` must mean the same at every backend (a model: a server-level reader slot,
  every backend's read lock with room for all of them); the retirement's model (the share at rest
  with `T`, which `Lock` takes; mvcc's writers never hold the auth share).

### Findings of the drafting and the glue

1. **The fuel does not survive a jump** (glue of `Recover` at the install). The apply thread's auth
   resource carries `authOwnFu` (`⧗ k`, the latest revision at most `k + 1`): after a jump the
   image's revision counts every admin entry of the committed log, the receipts only this member's
   applications. Drafted: the fuel at a base `b` (`authFuelB`, `b < 2^61`): an install sets `b` to
   the image's revision, below `2^61` by raft's index bound; `stepOk_of_fuel` keeps the `uint64`
   bound (`2^48 + 2^61 < 2^64`) and `permsFit` (`< 2^63`). A redefinition in place of
   `authApplyResAt`/`authApplyResB` (`authApplyResOn` in the Draft), boot at `b = 0`
   (`authFuelB_of_fuel`, proved).
2. **The lock's share** (above): the apply thread's auth resource must carry its token's
   retirement (`authApplyResOn`), from the premise that gave the token.
3. **`Recover.spec`'s post is too weak for the install**: its flag and cache halves are untied;
   the apply thread needs them tied to the new latest state (`tieRes`). `Recover.specP` gives it
   (what the code does: the flag and the cache are set from `stI`).
4. **The model's states must be well formed** (`srvHist_wf`, statement only): `permKeysOk` of every
   state of the committed log's history (the catch-up appends them to `authHist`, which keeps it),
   `permsFit`, `authSmall` and the revision bound of the image's state. To check against the model's
   admin steps; if the grant step's model admits an invalid permission range, the catch-up needs a
   premise instead.
5. **The rest model does not track the auth buckets** (`restModel`'s auth buckets stay `authBoot`:
   `restAfter` models only the cluster requests; the admin writes go through `AEnv.RW`). So
   `specSnap`'s `hA'` (the image's tracked buckets the rest model's) is false with auth on whenever
   the image holds users; `specSnapOn` restricts it to the non-auth buckets and takes
   `authBucketsAt` for them, but its post's `srvRest E' γr A'` (the rest buckets at the rest model)
   cannot be met: the mode-on meaning of `srvRest` (the tracked auth buckets at the auth model's
   state) is a pre-existing gap of the mode-on server, not of the install. For the user.
6. **What `run` must carry** (glue at `run`'s job): the store's snapshot clause with its invariant at
   the store's `R` (`srvAuthSnapOk`), as `bootOk`'s `#HmetaSnap`; the mode-on start chain
   (`γr.kv.ch0 = alarmChain true false false`); and the snapshot directory's image in the mode
   (`srvSnapRO`'s `snapDirInv` holds the mode-off `srvImage`; with auth on, `srvImageOn`: #7-on).
   The applied log's auth state comes from `applyResOn` (`kvRunAtOn_sa`, proved).
7. **The new backend's hook**: `authSchemaSnap` takes the hook frozen (`plHookRO`); the walk's open
   (`OpenSnapshotBackend` with the server's hooks) must give it (to check in J8b's walk).

### Glue proved (no `sorry` of its own; over the drafted specs)

- `authRecoverOn_glue`: `Recover`'s call at the install (`authRecoverOn.spec`, the mode-on twin of
  `authRecoverOk`) from `Recover.specP`, `authSchemaSnap`, `authHistTie_catchup`, `catchup_list`,
  `authLockRetire`, `authCatchUpFirst` and `srvHist_wf` (the only `sorry` it reaches besides the
  callee spec). The catch-up's ghost steps go through as drafted.
- `kvRunAtOn_sa`: `specSnapOn`'s `hsa` from `run`'s loop resource.
- `authSchemaSrv_of_G`, `authCatchUpFirst`, `authSnapC_of_snap`, `authFuelB_of_fuel`.
- Not glued: `applyAll.specSnapOn`'s body (the twin of J8a-5's proved `ApplyAllSnap.lean`) and
  `run_snap_jobOn` (the twin of J8b's job), which wait on J8b's shape; the install walk's mode-on
  steps besides `Recover` (`srvApplyKVOn`'s row at the new backend needs the admin steps at the new
  hook, `authStepsAtHook` from `authWAtHook`, as `authApplyResB_of_pre` at boot).
