# A1: the filled-value soundness argument (DRAFT, for the A1.5 stop; decision 5 of the A1 Scope)

Status: drafted at A1.4, completed at the A1.5 stop (2026-11-17), with the independent review of A1.4
(`/shared/tmp/auth-schema-srv/a1-soundness-review.md`: sound at A1.4; two MAJOR forward obligations, both
addressed below) folded in. Branch `auth-schema-srv`.

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
     too). **Open for A1.7**: today that proof takes both steps when `Unlock` starts (before the write-back,
     as since decision 3), which is harmless while no invariant links the flag to `tk`; once A1.7 adds "flag
     `false` ⇒ `tk n = idle`", the two steps must move to `Unlock`'s end (after the write-back, or the commit
     when one is due: the points where `tk` becomes idle), or the invariant be stated outside an `Unlock`;
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
   `batchLockedW` or the commit specs (all proved, internal).
3. **The accessor** (`rbAcc γ Sc ok Rr`, `ClaimedLemmas.lean`; the claimed `Unlock` statement
   `Unlock.specC`, `UnlockClaimed.lean`). It is the client's resource, run by `Unlock`'s proof at the
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
   accessor's buckets (premise `∀ n, st.cw n → n ∈ Sc`; in the client-facing `Unlock.spec` `cw` is empty by
   `cwOk`, the corollary at `Sc = []`), so no claimed bucket's readers' contents move without the client's
   halves; a claimed bucket outside `Sc` is untouched (`rbrOne`'s claimed branch: `tk idle ∨ cw`).
4. **`Unlock` with nothing pending** in a claimed session forgets the claimed writes (`BSess.clrCw`,
   `batchGhostAt_clr`): sound because every tracked bucket is then idle (`free_of_pend0`), and `cw` is ghost.
5. **Sealing** (review MINOR 1): `rbRd` and `rbrHalves` are not sealed; a client that unfolds `rtHeldF` can fold
   part of it into `rbRd` of an unclaimed bucket, but it then cannot `RUnlock` (it needs all of `rtRes rfrac`),
   and the facts it derives are true (the readers' contents). Harmless; sealing `rbrHalves` (`@[no_expose]`) is a
   form left for A1.9 (it would need `InvBackend` changed, ~2250 importers).
