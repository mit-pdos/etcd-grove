# Spec review: revoke-open, round 2

Reviewer: independent subagent, 2026-11-06. Branch `revoke-open` at `01663f666e` (worktree
`/shared/etcd-grove-leaseexp`). The round-1 fixes are `git diff 368a196acc 01663f666e`; the whole
branch is `git diff 35b63470a1 HEAD` (`35b63470a1` is `git merge-base lean HEAD`). The Go code is the
pinned fork (`/shared/etcd-grove/.lake/go-src/etcd`, `249d76bea7`; this worktree has no
`.lake/go-src`): `server.go:860-905` `revokeExpiredLeases`, `auth/store.go:1175-1178` `WithRoot`.
The only file I wrote is this one. I ran no build and no Lean.

What I checked without building:
- Every target's `.olean` under `.lake/build` is newer than its source.
- `.lake/tcb.json` (written after those `.olean`s) lists `sorries = []` for
  `EtcdServer.wp_revokeExpiredLeases`, `auth.authStore.wp_WithRoot` and `etcd_leaseexpiry_safe`.

So I take the files as built and the results as `sorry`-free. That is evidence, not a check of
record.

**Verdict: no BLOCKER.**
- Every r1 SHOULD-FIX is resolved, and so are seven of the eleven NITs. Of the other four, NIT 3.4
  and NIT 3.7 are deferred with reasons (plan, "Not done"), P1 was already fixed at `368a196acc`, and
  NIT 1.2 is stale.
- The new elimination laws are narrow: each gives one use's resources and none restates a sealed
  body.
- `WithRoot.spec` is true of Go and fits its one caller.
- New findings: one SHOULD-FIX (N1, `WithRoot.spec`'s free mode pinned by an equation) and seven NITs.

## The r1 findings, one by one

| r1 | Status | Fix introduced a new problem? |
|---|---|---|
| S1: bundle laws restate bodies | **Resolved.** `_parts` gone; `srvRevokeOuterPool`/`InnerPool` and new `srvRevokeOuterLoan`/`InnerLoan` are `@[no_expose]` (`RevokeCtx.lean:87,97,104,113`); one elimination per use (`:204-344`). The consumer no longer unfolds the pools, `srvGoAttachOk`, `apply.isAuthStore`, `auth.enabledVerdict`, `lease.expiredLeases`, `backend.rdPoolN` (`EtcdServer__revokeExpiredLeases.lean` greps: only `srvFieldsAt`, `srvRunFieldsAt`, `leaseRevokeReqRO`, `mvcc.counterSpec` remain) | Small leftovers: N3 (an unused `ihave`), N5 (`srvRevokeCtx_withRoot`'s proof unfolds `srvAuthAt`) |
| S2: hub over a server constant | **Resolved.** `srvStartReadN` with `one_le_srvStartReadN` in `InvStart.lean:62-72`; `srvStarted` (`:331`), `srvStartReaders` (`:343`), `start_gives_views` (`Results.lean:2254`) use it. `etcdstart.memberReadN := srvStartReadN` and its law is the server's, with no unfolding (`etcdstart/Defs.lean:335,339`; `interface/.../etcdstart/Defs.txt` shows `srvStartReadN`) | No. N6 notes what is left (the wait-group count) |
| S3: `WithRoot`'s premise implementation-shaped | **Resolved in form (b)**, with a checked reason for not doing (a). `NewAuthStore.spec`'s post gives an opaque `RD` and contracts, not `authInv` (`Spec/.../auth/NewAuthStore.lean:133-136`), and `authStoreKit_off` builds only from that (`AuthSrv.lean:304`). The 20 lines of glue are now one law, `srvRevokeCtx_withRoot` (`RevokeCtx.lean:304-324`), over `apply.isAuthStore_isAuthEnabled` (`AuthDerive.lean:445-458`) | N1 (the shape of the mode premise); N2 (the docstring does not say the departure) |
| S4: literal `4` twice | **Resolved.** `srvRevokeK` (`RevokeLevels.lean:20`, `@[word_unfold]`, a module importing only `Perennial.Std.Attrs`), used in `srvRevokeLevels` (`RevokeCtx.lean:67`) and in the four `Hprog`s (`interface/.../Adequacy.txt`, `AdequacyMembers.txt`) | NIT N4: two `4`s left (the proof's `hlev4`, a docstring) |
| NIT 1.1: Lean implications | Resolved (`EtcdServer__revokeExpiredLeases.lean` spec `:52`; `run` discharges it by `ipureintro`, `EtcdServer__run.lean:1330`) | No |
| NIT 1.2: half of `srvRevokesLeases` implied | Stale: the spec now takes `ρ.rd.kv.lm = .revocable` alone, and the proof derives the auth half (`:67-71`) | No |
| NIT 1.3: `show` unfolds `srvRevokeLevels` | Resolved: `srvRevokeLevels_of_max HT` (`leaseexpiry/Adequacy.lean:161`, law `RevokeCtx.lean:70`) | No |
| NIT 1.4: `run.spec` docstring names layout | Resolved | No |
| NIT 2.1, 2.2: docstrings | Resolved (`Adequacy.lean:8-11`, `Results.lean:2236-2240`) | No |
| NIT 3.1: `wp_GoAttach_tok`'s `srvLgReader` | Resolved (`GoAttachTok.lean:36-41`); the 12 uses (`Start` ×10, `sendMergedSnap`, `monitorLeader`) updated | No |
| NIT 3.2: `GoAttach`'s level | Resolved (docstring, `EtcdServer__GoAttach.lean:38-39`) | No |
| NIT 3.3: tautological conjunct | Resolved: `apply.AEnv.authMode_off_of_authOn` (`apply/Chain.lean:712`), a one-line law from `AuthMode.isOn_false_iff` | No |
| NIT 3.4: duplicated bound in `srvRevokeBuilt` | Not done (deferred). The consumer-shaped `srvRevokeCtx_bound` (`:280`) covers the use | Acceptable |
| NIT 3.5: `lease.bootCfg_revocable` unused | Resolved (deleted) | No |
| NIT 3.6: `authRdN` literal | Resolved: `rdPoolN + 2 ^ 7` (`RdPool.lean:58`); `rdStockN_val` unchanged | NIT N8 (one stale note) |
| NIT 3.7: `srvApplyLoopInit` positional; mvcc `Inc` law | Not done (deferred). Still `icases Hinit with ⟨-, -, ⟨-, -, -, ⟨%cnt, …⟩⟩⟩` (`:94`) and `iunfold mvcc.counterSpec` (`:250`) | Still open, low |
| P1: baselines | Resolved at `368a196acc` | — |

## Targets

### `RevokeCtx.lean`: `srvRevokeCtx`, its laws, the pools and loans, `srvRevokeCtx_withRoot`

**Good.**
- Both pools, both loans, `srvRevokeBuilt` and `srvRevokeCtx` are sealed. Their persistence
  instances are proved inside the module.
- The eliminations are narrow, one per consumption point:
  - `_outerBorrow` gives `srvWgReaderAt ∗ srvReadReader` and a loan, for `£ 1 ∗ levelTok 2`.
  - `_innerBorrow` gives `srvLeadTimeReader ∗ E.RD` and a loan, for `levelTok 1`.
  - The two give-backs return the level.
  - `_raftPool`, `_bound` (`threadBound GF ≤ 2 ^ 30 - 1`, exactly `ensureLeadership.spec`'s premise),
    `_views`, `_withRoot`, `_cred` and `_ctx` each give one thing.
  - None restates a body. A conjunct added to `srvRevokeCtx` changes `_intro`, `start`'s call to it,
    and the proof of the law that opens it. Nothing else changes.
- The intro laws take the pieces their builders hold:
  - `srvRevokeOuterPool_intro` takes a level-2 thread pool (`start`).
  - `srvRevokeInnerPool_intro` takes `leadTimeMu`'s slots in their own form (`NewServer`). It moved
    here, next to the definition.
  - `srvRevokeBuilt_intro` takes the pieces without the existential.
  - `srvRevokeCtx_intro` is the body, proved by `.rfl`. That is acceptable for an intro: it is what
    `start` has, and no consumer uses it.
- `start` now uses `srvRevokeOuterPool_intro` instead of `iunfold srvRevokeOuterPool`
  (`EtcdServer__start.lean:588`).
- `srvRevokeCtx_withRoot` gives exactly `WithRoot.spec`'s premise. The revocation's proof makes the
  call with a single `ihave`.

**No law exposes internals to another package.** The masks in the borrow laws name
`srvRevokeOuterN`/`srvRevokeInnerN` through a subset premise (`↑srvRevokeOuterN ⊆ Em`). The only
consumer, inside etcdserver, passes `⊤`. Nothing outside etcdserver mentions `srvRevokeCtx`'s laws
(grep), and etcdserver has no API list.

**NIT N5 (PRINCIPLES "A client does not unfold … any other module's").**
- `srvRevokeCtx_withRoot`'s proof (`:318-319`) does `iunfold srvAuthAt` (`AuthGuard.lean:181`) and
  destructures 9 positions to reach `isAuthStore` and the store pointer.
- It is a proof, not a statement, and the pattern is old (8 `iunfold srvAuthAt` in the tree).
- Fix: a law in `AuthGuard.lean`, `srvAuthAt_isAuthStore : srvAuthAt s E ⊢ ∃ st P f, srvAuthStoreAddr s
  ↦□ st ∗ apply.isAuthStore st … E.RD E.authMode …`. This proof would use it, and so could the next
  `iunfold`.

### `RevokeLevels.lean`: `srvRevokeK`

**Good.**
- One number, `@[word_unfold]`, in a module of its own. The adequacy lemmas import it without the
  server (`etcdstart/Adequacy.lean:31`).
- The 13 closed proofs switched `rw [HT]; omega` to `word`, because `omega` does not see through the
  name. Their statements are unchanged.

**NIT N4 (S4's two leftovers).**
- `EtcdServer__revokeExpiredLeases.lean:67`, `have hlev4 : 4 ≤ threadBound GF := hlev`, reads
  `srvRevokeLevels` by definitional equality with the literal. It is the owner's own constant, as
  the plan says, and it breaks loudly if `srvRevokeK` changes. Still, writing it as
  `srvRevokeK ≤ threadBound GF` and closing the level side-goals with `word` would make a new level a
  one-number change in the proof too.
- `Proof/runtime/Threads.lean:66-67`, `realThreadsBelow_mono`'s docstring, still says
  `max (n + 2) 4`.

### `InvStart.lean`: `srvStartReadN`, `one_le_srvStartReadN`

**Good.**
- The count is named where the slots are owned. Its law is proved there, with the unfolding of
  `srvRevokePoolN`, `rdPoolN` and the `actualMaxReaders` seal (`:69-72`) inside the owner.
- `start_gives_views`'s exported text no longer spells the revocation's pool.

**NIT N6.**
- The other half of `srvStartReaders`, the wait group's `actualMaxReaders - 2 - srvRevokePoolN`
  (`:333`, `:344`), stays literal. The plan says why: no client outside etcdserver names it. That
  holds of the statements.
- But the two hubs that take `Start`'s post do `iunfold srvStartReaders` (`etcdstart/Start.lean:74`,
  `etcd/auth/startServer.lean:190`; old, on `lean` too) and drop that half. They therefore see its
  body, and their framing into `memberUp` matches `memberReadN` against `srvStartReadN` by delta.
- An elimination `srvStartReaders_read : srvStartReaders s γr ⊢ [∗list] _ ∈ replicate srvStartReadN
  (), srvReadReader s γr` would close that. Low priority.
- **NIT N7**: `etcdstart.memberReadN` is now a pure alias of `srvStartReadN`, two names for one
  count. r1 allowed that ("that name or an abbreviation"). It is harmless, but the docstring could
  say that the alias exists only so that `memberUp`'s consumers name nothing of the server.

### `Spec/.../EtcdServer__revokeExpiredLeases.lean`

**Good.**
- True of `server.go:860-905`.
- The pure premises are one `⌜…⌝` conjunct (`:52`), and the lease mode is the only premise left from
  `srvRevokesLeases`. The auth half follows from `srvGrantGuard_expired` on the slice, which the
  proof applies (`:69-71`).
- `run` discharges the new premise by `ipureintro; exact ⟨hlm, hlev⟩` (`EtcdServer__run.lean:1322,1330`).
- The docstring records the change.

**NIT N3 (proof hygiene, not the statement).**
- `:75`, `ihave #Hauth := srvAuthAt_of_views …`, is now unused. `srvRevokeCtx_withRoot` does that
  derivation itself. It is dead.
- `:223`, `try (ipureintro; exact hM)`: a `try` around the one step that discharges `WithRoot`'s
  `⌜M = .off⌝` hides whether the step ran. Write it without `try` (or, with N1, the step goes away).
- `:219` documents the `wp_apply hWR` silent abort. That is the Perennial limitation r1 recorded
  (`notes/perennial-changes.md:1243`, the same class). It is fine as a workaround.

### `GoAttachTok.lean`: `wp_GoAttach_tok`; `InvGoAttach.lean`: `srvGoAttachOk_stopping`

**Good.**
- `wp_GoAttach_tok` takes and returns only `srvGoResAt s γ` and `P`. The header lists its callers
  accurately (`Start`, `sendMergedSnap`, `monitorLeader`; I found no `applyEntryNormal` use by grep).
- `srvGoAttachOk_stopping` (`InvGoAttach.lean:140-150`) is a narrow elimination. It gives the
  `stopping` channel's address and a receiver's `ownStopChan` (built from the protocol's
  `isStopChanInternal`), which is what the outer loop's `select` takes and nothing more.
  `srvGoAttachOk` itself stays unsealed, as on `lean`.

### `Spec/.../auth/authStore__WithRoot.lean`

**Does it say what Go does?** Yes. Under `⌜M = .off⌝` the contract's verdict `enabledVerdict .off b` is
`⌜b = false⌝` (`auth/Model.lean:812-816`). So `!as.IsAuthEnabled()` holds, and Go returns `ctx`
(`store.go:1176-1177`) with `RD` back. The root-token branch (`:1180-1210`) is excluded by the
premise, and without it the post `RET #ctx` would be false: at `.any`, or `.on` with auth enabled,
Go returns a derived context. So the premise is a real scope restriction, not an unneeded one.

**Is it usable by its callers?** Yes. There is one caller.
- `revokeExpiredLeases` gets the contract from `srvRevokeCtx_withRoot` in one line.
- It passes `E.authMode` for `M` and `hM` (from `authMode_off_of_authOn`) for the equation (`:221-223`).
- The same contract shape comes from the auth package's own `IsAuthEnabled.spec`, at
  `RD := enabledRd st M`, since `authInv` is persistent (`InvAuth.lean:1223`). So a future caller
  holding the real store's invariant can also meet it.

**SHOULD-FIX N1: a one-mode statement over a free mode pinned by an equation (PRINCIPLES, hard
rules, "A law over a free mode … holds at every value of it": "A law that holds at one mode only is
stated at that literal …, not over a free `on` with an `(h : on = b)` premise").**
- `∀ … (M : AuthMode) …, {{ … ∗ ⌜M = .off⌝ ∗ □ {{ RD }} IsAuthEnabled {{ b, RD ∗ enabledVerdict M b }} }}`
  (`:34-38`) is that pattern. It holds only at `.off` and is stated over a free `M` with the equation
  as a premise.
- Its effect is to spare the caller one rewrite.
- The mode gate (`etc/mode-check.py`, `SCOPE`) does not scan the auth package, so the rule's count
  argument does not bite here. But the shape costs a binder and a premise that say nothing beyond the
  literal, and a reader has to work out that `M` is not free.
- r1's S3 (b) proposed exactly this shape. r1 was wrong on this point.
- Restatement: `∀ (st : Loc) (RD : IProp GF) (ctx : GoInterface), {{ isPkgInit … ∗ RD ∗ □ ({{ RD }}
  st.IsAuthEnabled() {{ (b : Bool), RET #b; RD ∗ enabledVerdict .off b }}) }} st.WithRoot(ctx)
  {{ RET #ctx; RD }}`.
- Move the bridge to the law that already has the gate: state `srvRevokeCtx_withRoot` (it takes
  `h : E.authOn = false`) with `auth.enabledVerdict .off b`. Its proof rewrites by
  `apply.AEnv.authMode_off_of_authOn E h` before `iapply apply.isAuthStore_isAuthEnabled`.
- The caller's `try (ipureintro; exact hM)` and `hM` then go.
- Extending to auth on later is a change of the spec either way (the post gains the token branch).
  The free `M` buys nothing for that.

**NIT N2 (PRINCIPLES "say so when you knowingly depart"; "Know the margin").**
- The spec still takes the implementation's own call (`IsAuthEnabled`'s contract at `st`'s method).
  An implementation that read `as.enabled` under `enabledMu` itself would not meet it. The reason for
  keeping it is sound (the off-mode store is `NewAuthStore`'s axiom, with no `authInv`), but it is
  only in the plan.
- One docstring sentence fixes this: "Departs from an API spec: it takes `IsAuthEnabled`'s contract,
  because the server's off-mode store is `NewAuthStore`'s axiom, which gives contracts, not
  `authInv`; with the off-mode store proved, it takes `authInv st R M ∗ enabledRd st M` instead.
  `⌜…off⌝` is a scope restriction: the root-token branch is not proved."

### `apply/AuthDerive.lean`: `isAuthStore_isAuthEnabled`; `apply/Chain.lean`: `AEnv.authMode_off_of_authOn`

**Good.**
- `isAuthStore_isAuthEnabled` (`AuthDerive.lean:445-458`) is narrow. It projects `isAuthStore`'s
  `IsAuthEnabled` clause and fixes the interface value to the concrete method through
  `auth.authIface`. It is in the module that owns `isAuthStore`.
- `authMode_off_of_authOn` (`Chain.lean:712-714`) is the vocabulary law r1 asked for. It is true at
  every `E` (`AuthMode.isOn_false_iff`, `auth/Model.lean:389`; `.any` is on), and it lives next to
  `AEnv.authOn`.

### `lease/LessorBackend.lean`: `expiredLeases_read`

**Good** (`:163-178`).
- It gives the reader's part: the slice read-only, and each element non-null with its `ID`
  read-only. It drops the guard and non-emptiness, which `srvGrantGuard_expired` covers.
- It is in the lessor's module, so the server no longer unfolds `lease.expiredLeases` in the
  revocation.
- (`srvGrantGuard_expired`, `InvApplier.lean:513-520`, still unfolds `lease.expiredLeases`. That is
  old and outside the targets. A guard-side law `expiredLeases_guard : expiredLeases GA ls ⊢ ∃ id,
  GA id` would close it.)

### `etcdstart/Defs.lean`: `memberReadN`; `Adequacy`/`AdequacyMembers`: `max (n + 2) srvRevokeK`

**Good.**
- `memberReadN := srvStartReadN`, and `one_le_memberReadN := one_le_srvStartReadN`. etcdstart no longer
  unfolds `backend.rdPoolN`, `srvRevokePoolN` or `sync`'s seal.
- The four `Hprog`s name `srvRevokeK`, and the interfaces were regenerated (diff only in `Hprog`'s
  line breaks and the name).
- The closed theorems' statements are unchanged (`git diff 368a196acc HEAD -- '*Adequacy*'`: proofs
  only).
- See N7 for the alias.

### `backend/RdPool.lean`: `authRdN`

**Good.**
- `rdPoolN + 2 ^ 7`, the same value, says why, and stays in step with `srvRevokePoolN = rdPoolN - 1`.
- The coupling (a backend constant sized for the server) is stated in the docstring.
- `rdPoolN_add_rdStockN` and `rdStockN_val` are unchanged in text, and the interface diff is the body
  only.

**NIT N8**: `notes/decisions.md:32865` still writes `backend.authRdN = 2 ^ 28 + 2 ^ 7`. It is true in
value but now not the definition's text. Add "(written `rdPoolN + 2 ^ 7` since r1)" or leave it as
the entry's history.

## Go code

No bug found, and nothing for `issues/`. The only new Go-facing claim is `WithRoot`'s off branch,
which matches `store.go:1175-1178`.

## Ranking (most in need of revision first)

1. `authStore.WithRoot.spec` with `srvRevokeCtx_withRoot`: N1 (SHOULD: state it at `.off` and move
   the bridge into the server's law) and N2 (a docstring for the departure).
2. `revokeExpiredLeases`' proof: N3 (a dead `ihave`, a `try`), N4 (`hlev4`'s literal), and r1's
   NIT 3.7, still open.
3. `RevokeCtx.lean`: N5 (`srvAuthAt` unfolded in a law's proof).
4. `InvStart.lean` / etcdstart: N6 (the hubs unfold `srvStartReaders`; old), N7 (the alias).
5. `RevokeLevels.lean` / `Threads.lean`: N4 (a stale docstring).
6. `RdPool.lean`: N8 (a note only).
7. Good as they are: `srvRevokeCtx`'s eliminations and pools, `srvStartReadN`, `wp_GoAttach_tok`,
   `srvGoAttachOk_stopping`, `isAuthStore_isAuthEnabled`, `authMode_off_of_authOn`,
   `expiredLeases_read`, `memberReadN`, and the adequacy lemmas.
