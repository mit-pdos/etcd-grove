# C-I3: `bootstrapLeftContract.law` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/CrashInterim.lean`)

Review 2026-11-24, `axiom` skill, a fresh agent given the axiom and the fork (`768ecf158`; two scratch Go
tests in `server/storage/wal`). **Survives for now, suspect parts**:

- `walAreaUnsaved` (`walFiles … walFresh`) is **wider than `wal.Unsaved`**: `walRead` drops snapshot
  records above the saved commit, so a history of one `SaveSnapshot(5)` reads as `walFresh` while
  `Unsaved` is false (Go test: `Unsaved=false`, `ReadAll` empty) and Go restarts. Not producible today
  (`walRecs_closeAU` needs the unfiltered fold), but a crash-side producer could. To restate over the
  history (every operation a no-op `Save`) before it becomes an axiom; docstring corrected.
- The opaque `dataAreaDb0` disjunct: vacuous, but an opaque name in a trusted statement changes meaning
  when defined. **Removed**; T3 defines the data area's leftovers (must allow committed bucket creation,
  exclude torn meta pages and a backend holding applied entries).
- Likely hole in the fork's fix (code reading, no test): an unsaved WAL beside a backend with applied
  bootstrap entries is reachable; the fix's fresh branch is then wrong (`bootOk`'s consistent index 0).
  Needs a Go test and an `issues/` file; a fix: discard only when the backend's consistent index is 0.
- False at the pin: kept as a law (`abbrev … .law : Prop`), not an axiom, until the pin moves.

Survived: a state record with an empty `HardState`; a snapshot record at index 0 (narrower than Go, safe);
leftover `wal.tmp` (`RemoveAll` in `DiscardUnsaved` and `Create`); the resources' split (no double
count, satisfiable by `Create`+`Close`); `Unsaved`'s error paths.

## Re-review (2026-11-24, a second fresh agent): **survives, too narrow**
On one file system the new case (an unsaved WAL with the data area fresh) is unreachable: `bootstrapBackend`
creates the backend before `wal.Create`, whose directory sync commits the creation too. The useful leftovers
are a backend file (possibly with torn metas: `nonissues/bbolt-init-not-crash-safe.md`), which T3 must define.
A WAL `Unsaved` cannot read (kept, Go restarts) is excluded only through the WAL's whole-sector premise
(`SectorWhole`): to be stated. The snapshot-only history still reads `walFresh`: restate over the history.
