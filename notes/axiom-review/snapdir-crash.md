# The snapshot directory's invariant across a crash: the three axioms under the proposed body (2026-11-24)

Reviewed (D6 T6, branch `etcd-safe-d6t6/2026-11-24`, analysis by the D4c/T6 helper with the `axiom` skill's
method; no Lean change made): `snap.Snapshotter.SaveDBFrom.wp_proof`, `snap.Snapshotter.ReleaseSnapDBs.wp_proof`,
`storage.Release` (via `snapDirInv`), under the proposed body of `snapDirInv` (`notes/etcd-dist-d6.md` §T6):
`snapDirIs ∗ ((today's body with fileAtDur files) ∨ (crashed L ∗ snapCrashTok γd))`, the axioms' statements
unchanged.

## Verdict: **the proposed change is not enough; the crash law is unprovable under it** (no unsoundness found)

1. **`SaveDBFrom`'s post giving `fileAtDur` matches Go** (both syncs before return: `Fsync(f)` at `db.go:55`,
   `fsyncSnapDir` at `db.go:80`, the `ErrExist` branch also syncs the directory, `db.go:68-72`). OK.
2. **No axiom forges the crash disjunct**: none of the three gives `crashed L` (only the crash adequacy theorem's
   frame does) or `snapCrashTok` (a fresh token the crash frame keeps). OK.
3. **The gap: a crash inside `SaveDBFrom`.** The axiom is atomic at its return: the ghost directory changes
   (index added to `M` and `E`) only then. Physically, the file is linked under `<i>.snap.db` (`db.go:62`) before
   the directory sync (`db.go:80`). A crash in between leaves, on Linux, either nothing or the linked file
   (whole: the file was synced first) — a **stray**: present after the crash, but in the ghost state not in `M`,
   not in `E`, and its name still claimed free (`snapFree`'s `fileFree`). The new generation's names come from the
   crashed tree (`crashRest`, `osShared L' R V'`), where the stray's name is taken, so `snapFree` cannot be
   re-established for that index: `snapDir_crash.law` (which returns today's body at `L'`) is **false of the
   reachable states** and cannot be proved. Recording the stray in the new body needs its content's certificate
   (`□ img i D'` of the bytes it holds), which the crashed call's precondition had but no ghost state recorded.
   etcd itself is fine: a later `SaveDBFrom` of `i` keeps the stray (`ErrExist`), a whole image of the committed
   state at `i` (D22's finding 7), and the WAL never names `i` before `SaveDBFrom` returned.
4. **`ReleaseSnapDBs`/`storage.Release`** remove without a directory sync: a removed file may reappear after a
   crash. Under the body it is an untracked present file too (same shape as 3, but its index is in `E` with its
   removal fact `Rm`, so the new body can leave it untracked if its name's claim is not required): fine once 3's
   category exists.

## What would work (needs the axiom statements to change: a further trusted step)

* `SaveDBFrom` linearizes **at the link**: the index enters `M` with `fileAt` whose *bytes* are durable (synced
  before the link) and whose *entry* is not yet, and `E`; the post adds a persistent `snapDurable γd i` (the
  directory sync done). Body: a file of `M` is `fileAtDur` iff `snapDurable γd i`; `E \ M` holds `Rm i ∨ ¬durable`
  (pending/lost). After a crash, `M'` is the files that survived (each with its certificate, persistent), a lost
  index stays in `E` as lost (never durable, so never named by the WAL, which the receiver writes only after the
  return: the T2 invariant has to carry "the WAL's snapshot index is `snapDurable`").
* `snapDir_take` becomes a crash-token update (`|NC={⊤}=>`, `inv_nc_acc`); its two callers
  (`ApplyAllSnap.lean:141,637`) use `wp_ncfupd`.

Not tried: a Lean counterexample (none expected: the gap makes the law unprovable, not an axiom false).
