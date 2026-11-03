# The lease checks' revision re-check (item 3 of the lessor/auth list, 2026-11-01)

Spec-first, as `notes/lease-read-plan.md`. Branch `lease-revcheck`.

## Scope (2026-11-01)

**What the Go code does** (`server/etcdserver/v3_server.go` at the pin):
- `checkLeaseRenew` and `checkLeaseLeases` read `rev := s.AuthStore().Revision()` first and, on the
  per-key path only, fail with `auth.ErrAuthOldRevision` if `Revision()` differs at the end. The
  auth-disabled and admin paths return before the re-check.
- `checkLeaseTimeToLive` has no re-check: it returns `rev`, and its caller `LeaseTimeToLive`
  re-checks after `leaseTimeToLive` (only if auth is enabled then).

**What the specs say now**: each verdict (enabled, admin, each key's) is of some auth state no older
than the lower bound `n` held at the start (`*VerdictFrom M n`); nothing ties the verdicts to one
state. `revisionVerdictFrom M n rev` gives the start revision's state.

**Findings**
1. *The model has no "revisions strictly increase" fact.* `authHist`'s states carry a revision, and
   every `.next` step bumps it (`auth/Steps.lean`, `bump`), but no invariant records that the
   history's revisions strictly increase, so two reads of one revision do not identify one state.
   Any pinning needs that invariant first (auth package: every append, `authOwnF_revCur_append`).
2. *The re-check alone does not pin the verdicts to one state.* `commitRevision` makes the new
   revision visible (`atomic.AddUint64`) before `refreshRangePermCache` replaces the permission cache
   (`auth/store.go:712-713`, `849-850`; the cache has its own lock, the reader's read transaction is
   not the writer's batch lock), so a check can read the new revision, get a key verdict from the
   old cache, and read the new revision again. The model already allows this (`revFresh`: the
   cache of a state at an index at least the published one, not the revision's state).
3. *What keeps that window harmless in Go* is `isOpPermitted`'s own check of the token's revision
   (`revision < as.Revision()` fails with `ErrAuthOldRevision`, `store.go:873`) together with tokens
   being minted on the apply thread, sequentially with every auth mutation: a token usable in the
   window was minted before the mutation, so its revision is the old one and the check rejects it.
   `permVerdictFrom` records the first half (a state where `revision ≤ token's`), but nothing in the
   model records the second (tokens minted between mutations), and the two conjuncts are of possibly
   different states.

So "all verdicts at one auth state" is not what the lease checks' re-check gives by itself; it holds
(if it does) by a global argument about token minting that the model does not have.

## Draft, first finding (2026-11-01): the revisions do not strictly increase

The scope's chosen form ("weak form": a strictly-increasing-revision invariant on the auth history,
then the checks' posts restated with it) rests on a fact that is false in Go and unprovable in the
model:

- **`AuthEnable` does not bump the revision** (`server/auth/store.go:294-299` at the pin
  `249d76be`): it saves `enabled = true`, refreshes the cache and `setRevision(tx.UnsafeReadAuthRevision())`,
  the revision as stored, which is the current one (every `commitRevision` saves it). So
  `(disabled, r)` is followed by `(enabled, r)`; the model says the same (`authEnableF`: `.next
  {st with enabled := true}`, no `bump`). Not a Go bug: a token from before the last `AuthDisable`
  carries a revision below `r` (`AuthDisable` commits a revision), so `isOpPermitted` rejects it,
  and a check that read `r` while auth was disabled and then saw it enabled reads every verdict
  after the enable.
- **`Recover` installs the new backend's stored revision** (`store.go:406-407`,
  `authStore__Recover.spec`: `authOwnF M (hs ++ [sta])`, `sta` unrelated to `hs`). In Go a
  snapshot's auth revision is at least the current one only because every member applies the same
  entries in order and the auth revision is a function of the applied prefix; neither the auth
  model nor the server's snapshot-apply proof (`SnapApplyWalk`) has that, so "non-decreasing"
  across `Recover` would be a new assumption.

So the true invariant is "non-decreasing, and equal only across an `AuthEnable`", between two
`Recover`s. Options:

- **A.** Non-decreasing over the whole history, with a new premise on `Recover` (the backend's
  revision is at least the current one), assumed at the server (a trust-boundary fact about
  determinism of the applied prefix). Posts: on the key path every state between the start and end
  read has revision `rev`, i.e. the only step between is at most an `AuthEnable`.
- **B.** Epochs: non-decreasing between `Recover`s, no new assumption; the posts say "no bump step
  between the reads, or a `Recover` ran between": weak, and the auth invariant grows an epoch.
- **C.** No invariant: restate the posts with what the code observably does (the end read's verdict
  `revisionVerdictFrom` at an index at least the start's, with the same revision), and docstrings
  that the verdicts may be of a lagging cache and that equal revisions do not imply one state
  (`AuthEnable`, `Recover`). Cheap; little sharper than now.

**The user's choice (2026-11-01): C**, the posts only, then item 4.

## Draft (2026-11-01; superseded: see Review)

What the re-check observably gives: the end read's revision is that of a state at an index at least
the start read's, and both equal `rev`. Stating "at least the start read's" needs the second read to
see a state no older than the first, which the model does not give now: `revFresh` makes the atomic
the revision of a state at an index at least the *published* one, which may be older than the state
the first read saw. What does give it is the atomic's other half, `revCur`: with the admin side's
authority the atomic is the latest state's revision (`revCur_agree`). So:

1. **`revCur` (internal, auth `InvAuth.lean`)** records its quarter's history `hs` with its last
   state: `⌜hs.getLast? = some st⌝ ∗ authStateAt γa (hs.length - 1) st`, `st` the state whose
   revision the atomic is. Kept by the only two updates (`authOwnF_revCur_append`, `_keep`, which
   already make that `authStateAt`) and the allocation (`NewAuthStoreOn`). No spec changes.
2. **`auth.revisionReread M n x₀ x`** (new, persistent, `Fresh.lean`): in `on γa`, states at
   indices `n ≤ i ≤ j` with revisions `x₀` and `x`; `True` otherwise.
3. **`authStore.Revision.specAfter`** (new, `Fresh.lean`, proved there): a reader holding a previous
   read's verdict `revisionVerdictFrom M n x₀` reads `x` with `revisionReread M n x₀ x` (the atomic
   is the last state's revision, and the first read's state is in the quarter's history, so at an
   index at most the last).
4. **The posts** (sharper, nothing removed):
   - `checkLeaseRenew.spec`, `checkLeaseLeases.spec`: on `nil` through the key path, the keys'
     verdicts and `∃ rev, revisionReread M n rev rev`;
   - `LeaseTimeToLive.spec`: with `r.Keys`, besides the check, `enabledVerdictFrom M n false ∨ ∃ rev,
     revisionReread M n rev rev` (the re-check runs on every path, only if auth is enabled at the
     end; `checkLeaseTimeToLive.spec` is unchanged: it already returns the start read's verdict);
   - `LeaseLeases.spec` carries `checkLeaseLeases`'s new post (frozen 2026-11-01: a decisions.md
     entry).
5. **Docstrings** (the margins replaced): the re-check makes the start and end reads of one
   revision, the end's state no older than the start's; it does not make the verdicts of one
   state: each key's verdict is of a state no older than `n`, possibly of a cache older than the
   start read's state (`commitRevision` publishes the revision before `refreshRangePermCache`), and
   equal revisions need not be one state (`AuthEnable` keeps the revision, `Recover` installs the
   backend's).

**One more premise field.** The checks call `Revision()` through the server's auth store interface,
whose methods they get from `isAuthStoreLeaseLb` (`LeaseCheck.lean`, inside `srvAuthLeaseLb`, a
premise of every lease check: no proof builds it yet, the entry points' callers will). It gains the
second read: `□ ∀ x₀, {{ revisionVerdictFrom M n x₀ }} Revision() {{ x, revisionReread M n x₀ x }}`,
the real store's by `Revision.wp_after`, as its other fields are by the `wp_lb`s.

## Probe (2026-11-01)

The whole stage is small, so the probe is the proofs:
- `revCur`'s new conjunct: `InvAuth.lean` (`authStateAt_capped`, `authOwn_capped`,
  `authOwnF_revCur_append`; `_keep` keeps the history unchanged), `NewAuthStoreOn.lean` (the
  allocation: `hlast`, `Hst0`). No spec of the auth package changes.
- `Revision.wp_after` (`Fresh.lean`, `revCur_after`: `authHistRev_lookup` puts the first read's
  index below the quarter's length).
- `checkLeaseRenew`, `checkLeaseLeases`, `LeaseTimeToLive`, `LeaseLeases`: the second read through
  the new field, then `subst` of the branch's `rev = rev2`; `LeaseLeases` through `sep_mono_left`.
- Cross-package unfolds: none new (`revisionReread`, `revRecheckFrom` are unfolded only in their own
  packages' proofs).

## Review (2026-11-01) and outcome

An independent spec review (`spec-reviewer`) found the Draft's posts vacuous: `revRecheckFrom M n`
(`∃ rev, revisionReread M n rev rev`, two states `n ≤ i ≤ j` of revision `rev`) follows from the
first read's verdict alone (`i = j`; checked in Lean), so the restated posts would hold with no
re-check in Go, and nothing tied the key verdicts to either read. A non-vacuous form needs every
verdict bounded above by the end read's state (bounded variants of the permission, admin and enabled
verdicts and their auth specs), and would still be weak: a verdict can be of a cache older than the
start read's state. **The user's choice: revert to `lean`'s posts with a corrected margin** (no
spec, invariant or premise change), then item 4. The Draft's code (`revCur`'s last state,
`revisionReread`, `Revision.specAfter`, the extra row of `isAuthStoreLeaseLb`, the four proofs) was
built (`lake build` 0) and dropped. `checkLeaseRenew.spec`'s margin now says what the re-check does
not give and what protects Go (`isOpPermitted`'s token-revision check, tokens minted between auth
mutations); the other three specs cite it. No Go bug.
