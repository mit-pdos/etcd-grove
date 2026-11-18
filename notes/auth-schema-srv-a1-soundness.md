# A1: the filled-value soundness argument (decision 5 of the A1 Scope)

Status: drafted at A1.4, completed at the A1.5 stop (2026-11-17), with the independent review of A1.4
(`/shared/tmp/auth-schema-srv/a1-soundness-review.md`: sound at A1.4; two MAJOR forward obligations, both
addressed below) folded in; re-reviewed at A1.5 (`/shared/tmp/auth-schema-srv/a15-soundness-review.md`: sound,
no BLOCKER/MAJOR; its MINORs honoured below); §4.1's obligation discharged and §5 (the claim) added at A1.7,
§4.5 settled at A1.9 (2026-11-17). Branch `auth-schema-srv`.

## 1. What `OpenBackend`'s post hands out, and the new ghost

`storage.OpenBackend.wp_proof` (trusted) posts `newPostK` (`InvNew.lean`): `isBackend γ P W Pk b` (persistent),
`isStopChans`, `K γ`, `bViewC`, `plHook`, **`rbOwn γ (rbData P D)`**, the readers' tokens, `dlInit`, `fkCl`, `srSlot`.
A1 adds **no client resource** to it: the new ghost maps `γ.rbr` (each tracked bucket's readers' contents) and
`γ.rbc` (each tracked bucket's claim) live wholly inside `isBackend`'s lock resources:
- `γ.rbr`: the authority and one half of each element in the batch lock's free resource (`batchFree` →
  `batchGhostAt` → `trkSide` → `rbrSide`, sealed), the other half in `readTx.mu`'s resource (`rtRes` → `clnPart` →
  `rbrHalves`, and `rtCm` during a commit), split among readers by fraction;
- `γ.rbc`: the authority and every element whole at `none` (unclaimed) in `rbrSide`.
`rbOwn` keeps its text and meaning (the client's `γ.rbk` half of every tracked bucket).

## 2. Why it is allocatable

`backend.New.spec` is proved (`newBackend`, `NewAlloc.lean`): `rbr_alloc` allocates both maps over the tracked names
`rbDomOf P D` (fresh `GName`s, elements at the initial readers' contents `rvBkt P (D, ∅)` / `none`), and
`rbrSide_init` builds the lock's side (every bucket unclaimed, `cwOk` from `cw` empty). So `OpenBackend`'s post,
which claims what `New` gives (its standing argument), is realizable with the same names at every A1 step.

## 3. The axioms that take `isBackend` (texts unchanged)

What their texts mention of the backend's tracked-bucket vocabulary (`tcb-baseline` axioms whose spec names it):
- `schema.MustUnsafeGetAllLeases`: `batchLocked γ P b st` in and out at the same `st` (a reader). The client-facing
  mode (A1.4: `batchLocked … st` is mode `false`, `cwOk false st`) is passed through unchanged.
- `lease.NewLessor`, `auth.NewAuthStore`, `membership.RaftCluster.Recover`/`SetBackend`, `v3alarm.NewAlarmStore`/
  `AlarmStore.restore`, `schema.membershipBackend.MustRead/Save/DeleteMember…`: `rbPart γ S r` in, `rbOwnIn γ S r'`
  out (an **unclaimed** part made idle), or nothing of the tracked buckets.
- `backend.backend.Snapshot`: the observation is handed the lock's half `rbOwn γ r` (with the client's `R`, `W`,
  `Pk`) and concludes a pure `Q`. For a claimed bucket the lock holds both `γ.rbk` halves (`rbSide`'s and
  `rbrOne`'s), so `R` cannot hold a third; the observation gets nothing of `γ.rbr`/`γ.rbc`.
None mentions `rbPartR`/`rbOwnInR`/`rbRd`/`γ.rbr`/`γ.rbc`. These are sealed (`rbPartRF`, `rbrSide`, `rbrOne`
`@[no_expose]`; `rbRd`'s element only from the claim, A1.7), made only by backend-internal laws, and **no law turns a
claimed part back into `rbPart`/`rbOwn`/`rbOwnIn`**, so no axiom (all take the unclaimed forms) can write a claimed
bucket or move its readers' contents. A claimed part passed through an axiom's frame is opaque to it.

## 4. The obligations, at A1.5

1. **The claim law's invariant (A1.7) and the axioms that hand out `rbOwnIn`.** The claim (A1.7) turns
   `rbOwnIn γ {n} r` into `rbOwnInR` and `rbRd γ n ½ r`, which needs a lock-side invariant "a bucket whose
   `γ.rbk` flag is `false` is untouched by the session (`tk n = idle`), so its readers' contents are the
   part's" (not in `rbrOne` yet; A1.7 adds it). **No trusted axiom has to promise anything new for it**: the
   invariant is provable from the backend's proved code alone, and is an obligation on the backend proof:
   - every tracked write sets the flag (`rbSide_put`, `fun _ => true`), through either part (`rbWrite`);
   - the flag is cleared only by `rbSide_idle` (unclaimed part) and `rbPartR_idle` (claimed part, A1.5), both
     **private**, used only in `batchTxBuffered.Unlock`'s proof (`unlock_idle`/`unlock_idleR`, private there
     too). **Discharged at A1.7**: the invariant is `rbSide`'s new fact "a tracked bucket whose flag (the batch
     lock's half of its `γ.rbk` element) is clear satisfies `I`", with `I = tkI P st` ("`P.RB n → st.tk n =
     idle`") in `trkSide` (`trkHalf … (tkI P st)`). Every step keeps it: a write sets the bucket's flag
     (`rbSide_put`, `I'` from `I` elsewhere: the write changes no other kind); the write-back maps an idle kind
     to idle (`tkWb`, premise `hkI` of `trkSide_updR`); the commit makes every kind idle; the hook keeps the
     kinds (`trkKept`). The two idle steps moved to `Unlock`'s end (`trkSide_idle`/`rbPartR_idle`, private, in
     the macros `bu_free`, `bu_free0` and `bu_release` of `batchTxBuffered__Unlock.lean`, just before
     `batchTx.Unlock` releases the lock), where the free state's `freeOk` makes every tracked kind idle;
     `rbSide_idle` now needs `I'` of the buckets it clears, so it cannot run earlier. `unlock_idle`/`unlock_idleR`
     are gone.
   - `kOk .idle` then gives that the readers see the writer's contents, `r` by `rbSide_agree`.
   The axioms whose posts carry `rbOwnIn` (`lease.NewLessor`, `auth.NewAuthStore`, `membership.RaftCluster.
   SetBackend`, `v3alarm.NewAlarmStore`/`AlarmStore.restore`, `schema.membershipBackend.MustSave/Delete…`)
   get it from their own `Unlock` in Go (checked by the review against `lessor.go:808-814`, `store.go:972-1001`,
   `membership.go:50-81,171`, `alarms.go:112-122`): each post can be rebuilt from the proved
   `Lock`/`Unsafe*`/`Unlock` specs at `c = k = false`. `Recover`/`MustReadMembersFromBackend` take and return
   `rbOwnIn` (readers). `backend.Snapshot` returns no `rbOwnIn` (its observation concludes a pure `Q`), so it
   is outside this obligation.
2. **The mode.** The client-facing `batchLocked` (every trusted text's) now carries `cwOk false st` (no
   claimed writes outside the hook's window): in the **pre** of the one trusted text that takes it
   (`schema.MustUnsafeGetAllLeases`, a pass-through reader) as well as in posts; the hooks' contract
   (`hooksSpec` in `isBackend`) asks a hook to keep `cw` (`trkKept`), which the server's hook meets. A1.5 does
   **not** weaken `cwOk false`: the state between `Unlock`'s write-back and its commit (lock held, `hw = false`,
   claimed deletes recorded in `cw`) is carried in the claimed mode `true` through `batchLockedW`/`batchGhostW`
   (`(c : Bool := false)`, A1.5) and the `commit`/`unsafeCommit` specs (trailing `c Sc Rr`); the commit
   switches to the client-facing mode only inside the hook's window (`hw = true`, where `cwOk false` holds
   trivially: `batchLocked_setHw_mk`), and the commit resets `cw`. No trusted text names the mode `true`,
   `batchLockedW` or the commit specs (all proved, internal). Clients can enter mode `true` (`batchLocked_claimed`, over the public
   `trkSide_mode_up`, `false → true`); the general mode step `trkSide_mode` is private (A1.9 review MINOR 1, made
   private at A1.8's rename): only `Unlock`'s proof goes from `true` back to `false`, and it does so only where
   `cw` is empty. The one other public mode law, `trkSide_mode_win`, changes the mode inside the hook's window
   (`hw = true`), where `cwOk` holds in both modes; since `batchLocked`/`trkSide` are exposed, a client can still
   rebuild a mode-`false` lock by hand from a mode-`true` one whose `cwOk false` holds, i.e. outside the window
   only with `cw` empty, which is exactly the client-facing state (harmless: the review's MINOR 1). Mode `true` is
   harmless, since the mode `true` grants nothing without a claimed part
   (`rbPartR`, made only by the claim, §5), and with no claimed part (`Sc = []`) `Unlock.specC`'s premise
   forces `cw` empty (the corollary `Unlock.spec_free`), which holds as only writes through a claimed part set it; the mode `true` can never reach
   a trusted text, which all take mode `false`.
3. **The accessor** (`rbAcc γ Sc ok Rr`, `ClaimedLemmas.lean`; `Unlock.spec`, the one statement since
   A1.8, with the client-facing statement its corollary `Unlock.spec_free`, `UnlockBare.lean`). It is the client's resource, run by `Unlock`'s proof at the
   write-back's and the commit's ghost updates (inside `readTx`'s write lock, before `cacheInv` opens), and
   it can only move a claimed bucket's readers' contents to **what the readers then see**: the update
   (`trkSide_updR` → `rbrSide_stepR`) sets each element of `γ.rbr` to `rvBkt P rv' n`, the readers' state after
   the step, from both halves (`readTx.mu`'s, held whole under the write lock, and the client's); no other value
   can be written, since the element's other half is `readTx.mu`'s at `rvBkt P rv' n` from then on. What the
   client may count on (`unlockOk P st`, proved at the write-back by `unlockOk_wb`, at the commit as the
   writer's contents by `trkOk_commitG`): the writer's contents; a bucket untouched or only deleted from, kept
   (the write-back leaves it; the commit then moves it to the writer's); a bucket both put into and deleted
   from (`mix`), at the write-back the **intermediate** contents `rvBkt P (st.C, writebackR st.W st.R) n` (the
   puts over the old readers' state, the deletes not yet committed), not the writer's contents (review MAJOR 2:
   the `authReadTxOk` family of false one-state reads). Every claimed write of the session is among the
   accessor's buckets (premise `∀ n, st.cw n → n ∈ Sc`; in the client-facing `Unlock.spec_free` `cw` is empty by
   `cwOk`, the corollary at `Sc = []`), so no claimed bucket's readers' contents move without the client's
   halves; a claimed bucket outside `Sc` is untouched (`rbrOne`'s claimed branch: `tk idle ∨ cw`).
4. **`Unlock` with nothing pending** in a claimed session forgets the claimed writes (`BSess.clrCw`,
   `batchGhostAt_clr`): sound because every tracked bucket is then idle (`free_of_pend0`), and `cw` is ghost.
5. **Sealing** (review MINOR 1; settled at A1.9): `rbRd` and `rbrHalves` are sealed (`@[no_expose]`), so a
   client outside the backend (no `import all`, `etc/api-check.py`) cannot fold a part of `rtHeldF` into an
   `rbRd`; `rbRd` is made only by the claim (§5) and used through its laws (`ReadLemmas.lean`, which now
   `import all`s `InvBackend`). Before sealing the forgery was already harmless (§4.5 at A1.5: a client that
   did it could not `RUnlock`, and the facts it got were true).

## 5. The claim (A1.7)

`batchLocked_claim` (`ClaimedLemmas.lean`): `batchLocked γ P b st c ∗ rbOwnIn γ (· ∈ Sc) r ⊢ |==> batchLocked γ P b st c
∗ rbOwnInR γ (· ∈ Sc) r ∗ [∗list] n ∈ Sc, rbRd γ n ½ (bktOf r n)`, for `Sc.Nodup` buckets of the table that are
tracked (`P.BT`, `P.RB`); proved per bucket (`trkSide_claim1`) and by induction (`trkSide_claim`). Why each
output is true of Go:
- `rbRd γ n ½ (bktOf r n)`: the client's idle part's flag is clear, so the lock's is (`rbSide_agree_inI`), so
  `st.tk n = idle` (§4.1's invariant), so by `trkOk`'s idle clause (in `bgOk`, always) every reader of the
  current readers' state sees the writer's contents, which the idle part's `r` agrees with (`rvBkt_idle`). The
  readers' element moves from the batch lock's side (`rbrOne`'s unclaimed branch) to the client unchanged.
- `rbOwnInR`: half of the bucket's `γ.rbc` element, newly `some (r n, false)`; the batch lock takes the other
  half and the client's `γ.rbk` half (`rbrOne`'s claimed branch). A bucket already claimed has no idle part
  (`rbr_claimed_excl`: three `γ.rbk` halves), so a claim cannot be repeated or forged from a claimed bucket.
- The trusted texts: none takes or returns `rbOwnInR`/`rbRd`; the axioms that return `rbOwnIn` (§4.1) are
  rebuildable from the proved `Lock`/`Unsafe*`/`Unlock` at `c = k = false`, and `Unlock` still returns
  `rbOwnIn` (now from its end), so a claim of a bucket such an axiom handed out is as sound as one of a bucket
  the client wrote itself.
- A claim inside the hook's window (mode `false`, `hw = true`) is allowed: the bucket's kind is idle, so the
  commit leaves its readers' contents (`rvBkt_commit_idle`), and `rbrOne`'s claimed branch (`tk idle`) holds
  for a claimed bucket outside the commit's accessor list.
- The claimed parts' flags (A1.9 review MINORs 2 and 3). `rbPartR_idle` (private, run only at `Unlock`'s end)
  clears the `γ.rbc` flags of the claimed part handed in; it takes `trkSide_idle`'s premise (the part's buckets
  untouched, `tkI`), unused by its proof, so that a later law reading a readers' fact off `rbOwnInR` stays sound.
  Today no law reads a claimed flag being clear: `rbOwnInR` grants nothing beyond `rbPartR`. A6 must not derive
  a readers' fact from `rbOwnInR` without such a premise at every place it is made. The **`γ.rbk` flag** of a
  claimed bucket is set by its claimed writes (`rbSide_put` in `rbrSide_writeR`) and **never cleared**: `tkI`
  constrains only a clear flag, so this is sound, but nothing may rely on a claimed bucket's `γ.rbk` flag (it
  says nothing about the bucket's kind).
- A6's constraint (review A1.5 MINOR 3): `rbAcc` runs at mask `⊤` inside `readTx`'s write lock; the client's
  resource `Rr` and accessor must not need `cacheInv` or `readTx`.

## 6. A6.2: the claim without the batch lock (2026-11-17; supersedes §5's claim)

Scope `notes/auth-schema-srv-a6-claim-scope.md` §R (two independent reviews, GO by etcd-grove-03). Lean:
`InvBackend.lean` (`rbClaimU`/`rbClaimC`/`rbClaimOne`, `rbClaimInv` in `inv rbClaimN`, `rbClaimToks`), the laws in
`TrackedLemmas.lean` (writes, flag clears) and `ClaimedLemmas.lean` (`rbOwnIn_claim`, the steps of the readers' state,
the claimed flags, the token laws). `batchLocked_claim`, `trkSide_claim1`, `trkSide_claim` are gone (no twin).

- **The law.** `rbOwnIn γ (· ∈ Sc) r ∗ rbClaimToks γ P (· ∈ Sc) ={E}=∗ rbOwnInR γ (· ∈ Sc) r ∗ [∗list] n ∈ Sc,
  rbRd γ n ½ (bktOf r n)` (`↑rbClaimN ⊆ E`). The token carries the invariant, so the law needs no `isBackend`
  (a form decision: `isBackend`'s text and meaning are unchanged, unlike §R's first plan).
- **Why the readers see `r n`.** The claim invariant's unclaimed branch keeps the link `f = false → v = c.getD ∅`
  between its `γ.rbk` half `(c, f)` and its `γ.rbr` quarter `v`; the client's idle quarter agrees `(c, f) = (r n,
  false)`. The link holds at every step that changes `c`, `f` or `v` of an unclaimed bucket: a write sets `f`
  (needs the invariant's half: client ¼ + lock ¼ + ½); `rbSide_idle` clears `f` only at `Unlock`'s end, where the
  bucket is idle and `trkOk` gives the readers' contents (`rvBkt_idle`), which the lock's `γ.rbr` quarter agrees
  with; the steps of the readers' state (`rbrSide_stepR`) move `v` only for a touched bucket outside the claimed
  list, whose flag is set (`tkI`, below), so the link holds vacuously.
- **Once.** The token is half of the `γ.rbc` element at `none`; the claimed branch holds `some`, so a second
  claim refutes itself, and `New` allocates one token per bucket (`newPostK` hands them out, `newPostK_pool` passes
  them beside `newPostKP`, which holds none). The batch lock never holds a token: `Close` hands none out.
- **The lock's view (M1, form decided by the agent, differs from §R.2).** A claimed write leaves the `γ.rbk` flag
  **clear** (the claimed branch states `f = false`) and records itself in `st.cw`; `tkI` became `tk n = idle ∨ cw n`.
  So a touched bucket with no claimed write has its flag set, hence is unclaimed (the claimed branch's ¾ at
  `false` disagrees), which is what the steps of the readers' state need, with no relation between the claim
  marker's flag and `st.cw` (§R.2's `w.2 = f` coupling is not needed; MINOR 3 of the A1.9 review disappears: the
  claimed `γ.rbk` flag is never set). `rbPartR_idle` still takes the idle premise (A1 review MINOR 2), unused.
- **A claimed `UnsafeCreateBucket`** sets the claim marker's flag but not `cw` (a completeness gap, the second
  review's MINOR 3): such a bucket need not be in `Unlock.specC`'s `Sc`, and its `rbOwnInR` may come back only
  from a later `Unlock`. A6 creates no claimed bucket (`CreateAuthBuckets` runs before the claim).
- **Forbidden future laws** (second review MINOR 1, decided by etcd-grove-03; also in `bStopView`'s and
  `rbOwnInR`'s docstrings): (i) any exclusivity law between a claimed resource and a `γ.rbk` share (e.g.
  `rbOwnInR γ {n} r ∗ rbPart γ {n} r' ⊢ False`); (ii) any reader law or axiom taking `rbOwnIn` without `bOpen` or a
  held read lock; (iii) anything re-opening a closed backend under the same ghost names while `bStopView`'s share
  is held; (iv) any law updating a bucket's `γ.rbk` element (contents or flag) from client-shaped shares plus the
  claim invariant or a token without `rbSide` (after `Close`, the stale lock quarter + a client quarter + the
  invariant's half make a whole element; delta review MINOR 1, decided by etcd-grove-03). After `Close` a client may hold the stopped lock's client-shaped quarter of a claimed bucket; it is
  harmless only because none of these exists.
- **Trusted texts.** `rbPartF`'s fraction (½ → ¼, uniformly, so the lock still holds one `rbOwn`-shaped share,
  `backend.Snapshot`'s observation); `OpenBackend`'s `newPostK` gains the tokens (standing argument: `New`'s proof
  allocates them, `NewAlloc.lean`); `authRdSlots` gains the auth buckets' tokens (`authSchemaSrv`/`authSchemaSnap`'s
  premise asks more). `newPostKP` is unchanged, so no exported result whose precondition holds `newPostKP`
  changes (the second review's MINOR 2 does not arise).
