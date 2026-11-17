# A1: the filled-value soundness argument (DRAFT, for the A1.5 stop; decision 5 of the A1 Scope)

Status: draft written at A1.4 (2026-11-17) from the ghost as it stands; to be completed at A1.5 (the `Unlock`
accessor) and reviewed independently before any proof past A1.5. Branch `auth-schema-srv`.

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

## 4. Open for A1.5/A1.7 (where the review should attack)

1. **The claim law's invariant and the axioms that hand out `rbOwnIn`.** The claim (A1.7) turns `rbOwnIn γ {n} r`
   into `rbOwnInR` and `rbRd γ n ½ r`, which needs a lock-side invariant "an idle part (flag `false`) is untouched by
   the session (`tk n = idle`) and the readers' contents of `n` are the part's" (not in `rbrOne` yet). Every source of
   `rbOwnIn` must then establish it: `Unlock` (proved) does; the trusted `NewLessor`/`NewAuthStore`/`Recover`/
   membership/alarm axioms that return `rbOwnIn` promise it implicitly. Their Go argument (they end with their own
   `Unlock`, which writes the session back, and commits a pending delete) is the same fact; check each ends with its
   own `Unlock` (none returns `rbOwnIn` from inside a caller's session).
2. **The mode.** Client-facing `batchLocked` (every trusted text's) now also says `cwOk false st` (no claimed writes
   outside the hook's window): stronger in a post, so the hooks' contract (`hooksSpec` in `isBackend`) asks a hook to
   keep `cw` (`trkKept`, ledger addendum), which the server's hook meets (it writes `meta` through an unclaimed part).
3. To be added at A1.5: the accessor's statement and why it cannot be used to move a claimed bucket's readers'
   contents to anything but the writer's (`new` by kind, D2).
