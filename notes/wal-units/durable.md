# W4c U2 (`examples/lib/durable` over `fsExt`), fifth session (branch `wal-c-durable`, 2026-11-14)

Continues `notes/wal-fsext-w4c-plan.md`, "W4c U2 log" (four sessions). No axiom, no `sorry`, nothing
trusted changed, no Go changed. `Write.spec`/`Read.spec` unchanged.

## State of the unit

All of U2's proofs are done (sessions 1-4, all on `wal-int`): `durable.Read`, `tryRead`, `Write`, `tryWrite`,
the package initializer, the link (`etc/gen-link.py --durable`, 29 results; `wp_Read`/`wp_tryRead` take the
WAL's pending hypothesis `h_errors_IsPathErrnoNotExist`, `wp_Write` closed), the boot (`durBoot`,
`durBoot0` = the tester's `DurBoot0`), and the crash lemma `durInv_crash`. What was left is the **hD open
point**: how the tester's crash obligation meets `durInv_crash`'s premise `hD` when it also calls the WAL's
`walInv_crash`.

## Made this session (`LinuxFs/Proof/.../examples/lib/durable/Crash.lean`)

- **`durInv_crash` says where its own takes are named** (statement change; no importer outside durable): the
  pure post gains `∀ i ∈ D', V'.now.entry f.J f.b = some (.file i) ∨ V'.now.entry f.J f.tb = some (.file i)`
  (`durCrash_tmp` gains the same for the temporary). So a crash lemma called after it can show its own takes
  are not in `D'` by unique naming, when they are named elsewhere.
- **`durInv_crash0`**: `durInv_crash` at `D = []` (called first): no premise on taken files.
- **`durCrash_hD`**: `hD` from `∀ i ∈ D, ∀ J b, V'.now.entry J b = some (.file i) → J ≠ f.J` (every file taken
  so far unnamed in the new tree, or named in another directory). Pure, trivial.

## The hD open point: analysis, and what is left (for the WAL's owner; not decided here)

Neither crash lemma can be called after the other without changing the WAL's:

- `walInv_crash` (`LinuxFs/Proof/.../storage/wal/Crash.lean:120`) takes `crashRest … []`, so it must come first;
  its `D` is the area's boot files (named under `jr`: fine, `durCrash_hD` by unique naming, given that `f.J = jo`
  is no directory of the area, a `TreeWf` fact of two distinct roots for the tester) **and every old segment
  (`crashRest_take_segs` takes all of `segsAll Ls`, named or not)**. An old segment's inode named at
  `(jo, .durable-state)` in the new tree is excluded by nothing the tester holds: durable's invariant holds a half
  `osMeta` of each candidate (so a candidate could be told apart from a segment by validity, if the WAL returned
  its kept `segResF`), but **not of the temporary**, whose `osMeta` is the writer's and lost at the crash. So
  option (b) of session 4 (the WAL returning the old segments' resources) fixes the name `f.b`, not `f.tb`.
- With durable first (`durInv_crash0`), the mirror: the WAL's segments must avoid durable's `D'`; same gap for the
  temporary.

**Recommended (a'): the WAL takes only files it boots from.** `walStart`'s `is` needs only the new layouts'
segments (at `.wal` names in the area) and the boot files; an old segment not named in the area is never used
by the next generation. Change `walInv_crash` to take `crashRest … D` with the premise "every file of `D` is
named only outside the area's directories, or unnamed", and to take (fileStart) only the old segments that are
unnamed or named in the area, getting the pure crash facts (`SegCrashAt`, which `walCrash_pure`'s `hfiles` needs
for every segment) from a non-taking variant of `crashRestAt_take_segs` (the facts come from the old authorities
and `OsCrash`, which `crashRest` holds whatever `D` is; only the `fileStart` transfer needs `i ∉ D`). Its post
then says its `D` is unnamed or named under the area, which gives durable's `hD` through `durCrash_hD`; and in
the other order durable's new location post gives the WAL's premise. Either order then works, with no
cross-client exclusivity. Cost: a split of `crashRestAt_take_segs` (`CrashTakeSeg.lean`) and `walInv_crash`'s
filtering (the `is` list, `hperm`); `walStart` unchanged. Owner: the WAL's crash (`wal-u3*`); the tester
(`wal-c-tester`) then calls them in either order, needing `jo` not an area directory (`TreeWf`, distinct roots).

Rejected: (b) the WAL returning `segResF` (fixes `f.b` only, see above); keeping a half `osMeta` of the temporary
in `durInv` (its writes need the whole `osMeta`; a redesign of `tryWrite`'s four steps, and a deleted
temporary's inode is still in `ht`'s versions).

## Next

- The WAL's side of (a') (above), then the tester's `tester_crash` over `walInv_crash` + `durInv_crash`/`durBoot`.
- When Perennial's `errors-facts` proves `errors.IsPathErrnoNotExist`, move its spec from
  `wal/ExistCallees.lean` to `LinuxFs/Spec/errors/` and close `wp_Read`.
