# Plan: the snapshot install with auth on (`applySnapshot` in mode `on`; spec-first)

**Status (2026-11-01): Scope.** Started at the user's request ("start on the auth-on install
spec"), branch `snap-auth-on` (worktree `/shared/etcd-grove-snapon`). This note is Scope's output:
what the mode-off install spec assumes that fails with auth on, what exists, and the design
questions (Q1-Q4) to settle before the Draft. No Lean yet.

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
applied. With Q1 (b) the catch-up records it before `Recover` (so `Recover` appends it a second time,
harmless: the latest state is unchanged). With Q1 (a), the install records it first the same way.
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
