# Unit `create`: `wal.Create.wp_proof`'s cleanup arms (branch `wal-c-create`, base `wal-create25`, 2026-11-14)

The W4 log's twenty-eighth session, written here (the coordinator integrates it into
`notes/wal-fsext-plan.md`).

## The choice: design P (registration at success only)

The twenty-seventh session showed that option (a) (unregister `nm` after `cleanupWAL`'s `Close`) cannot give
`Create` the whole program half of `nm`'s claim back: the registration hands a fraction to `nameShare`, which
lends unknown amounts (`walInv_dirPath`) that borrowers drop. It proposed (R) lends returned at unlock and (P)
registration only at success. **P is chosen**, for these reasons:

1. **What is needed is narrower than the log said.** `cleanupWAL` has three outcomes past `w.Close()`:
   - `Close` fails (the sync failed: the locks and the handle stay, no rename): nothing moved; `Create` can
     register `nm` then (any fraction will do: `nameShare` keeps `∃ q`) and give `walAreaRes` back as
     `renameWAL`'s committed-error arm (arm 4) already does (`walInv_register`, `create_areaBack`);
   - `Close` succeeds, the rename fails: the same;
   - `Close` succeeds, the rename succeeds: the WAL's directory is moved aside to `nm.broken.<t>`.
   But `os.Rename.specDirAnySnc` takes the **whole** claim on `nm` (`q + r = 1`) before the call, whatever the
   outcome, so every path past a successful `Close` needs the program half whole. Only that needs a design.
2. **Under P nothing is ever lent from the pending name but by `Create` itself.** Until the registration the
   pending name's program half is `Create`'s (`walNamesRes`'s `o = some dir`: the invariant already supports
   this state, "until it registers, `Create` holds the whole program half, which its cleanup's rename
   needs"), and the only paths to `dir` are the two `Create` makes with its spine law (`create_spine`: `own d`
   each, `d + (d + c) = ½`), one in the handle's `walDirH`, one in the pipeline. Pinning their fractions in the
   handle before naming (`walOpenWFU … Rp qp`) and returning them from `Close.specU` gives `d + d + c = ½`
   back by arithmetic. No ledger, no change to any borrower.
3. **R touches the proofs other units own** (`WAL.Close`, `Exist`, `Open`, `openAtIndex`, `openLast`,
   `ReadAll`, each returning what it borrowed, and `walDirH`'s path made receipt-carrying in its ~13
   destructuring modules), while four other agents work on those modules; P touches `Handle.lean`'s
   parameters (defaulted: existing callers unchanged), `CreateHandle`, `HandleUnnamed`, `CloseU`, the
   names-free unlock lemmas, and `Create`.
4. **Arm 2 (the retry in `renameWALUnlock`) costs P nothing extra.** P needs `renameWALUnlock`'s reopen to
   build a pending handle from `Create`'s fraction (an `Open` variant over a pending WAL); but that variant is
   needed under either design, because `Open.spec` asks for a client atomic update on `walDirIs dir` that
   `Create` does not have after its commit (ledger 2026-11-14, "(2) Create-specific: blocked on `Open`'s
   update"). `renameWALUnlock.spec` is a hypothesis (false as stated, below); under P its arm 2 states the
   pinned pending handle, which is what such a variant would return.
5. The twenty-seventh session's finding that the naming must move after the parent's close fits P: the
   registration and the naming both happen at the success exit, after `dirCloser()`.

Not chosen, and why: (R) above; a "lend counter" in `walNamesRes` for the last registered name (R's cost for
one name, still needing every borrower to return).

## What P does (the plan)

- `Handle.lean`: `walDirH`'s naming fact `nmd` becomes a function of the path's roots and fraction
  (default `fun _ _ => walNamed dir`), its names fragment a parameter `nf` (default `none`); `walPipeH` a
  pin `pp` on its roots and fraction (default `True`); `walHandleIn`/`walHandleC` pass them. Defaulted, so
  every existing use is unchanged. `walOpenWFU P Mr w dir Rp qp`: `nmd := ⌜R = Rp ∧ q = qp⌝`, `nf := some
  dir`, `pp := R = Rp ∧ dq = own qp`.
- `create_ghost`: no registration; `createUH x qh` keeps `Create`'s whole remainder `c` with `c + qh + qh = ½`
  and the split record `Wn` (not `nm :: Wn`).
- `create_named_cont`: at the success exit (after `dirCloser()`), `walInv_named` and `walInv_register`, the
  handle sealed into `walOpenWF` (`walOpenWFU_seal`: the names fragment swapped, the pins forgotten).
- `Close.specU`: success arm returns, instead of `walUnlockedTok`, its pieces but the names fragment
  (`walUnlockedTokX`) with `walNamesFrag (some dir)`, and the two pinned paths; error arm `walLockedTok ∗
  walNamesFrag (some dir)`.
- `cleanupWAL` (spec and proof), and `Create`'s three cleanup sites: register-and-merge-back on the two
  outcomes without a rename; the moved-aside outcome needs the invariant step below.

## The moved-aside step (the last piece)

After a successful cleanup rename `nm → nm.broken.<t>` (the client's abstract state keeps the fresh,
unnamed WAL at `dir`: `Create` has no client fragment to change it), the invariant must hold with `nm`
absent and the WAL's directory at the broken name:
- `WalsOk`/`CrashOkW` hold (a crash keeps the rename: `nm` absent, `CrashTo`'s left disjunct since `named =
  false`; drops it: `nm` holds `J` as before); `AbsentOk`/`AbsentNone` untouched (the broken name holds a
  `.`, so it is no WAL name); `DirsAvoid` covers both names (`AreaSlot`); `WalsNamed`, `DirKeysOk` untouched.
- `WalsAt` fails for this WAL (its name holds nothing): an exception for the pending WAL is needed. Proposed:
  `walInvBody`'s `⌜WalsAt jr Ls cl⌝` becomes `⌜WalsAt jr Ls cl⌝ ∨ ∃ dir, ⌜WalsAt jr (delete dir Ls) cl⌝ ∗
  walNamesFrag (some dir)` (the invariant keeps `Create`'s names fragment: then no one can form
  `walNamesFrag none`, so every user of `WalsAt` refutes the right disjunct from the fragment it holds, and
  no lock token can ever be formed again in the generation, consistent with the error arm's losing it).
- `walAreaRes` must hold the broken name's claim without its subtree (the WAL directory's claims are the
  invariant's: `WalsOk`): its `∀ nm sfx, N.Mem (nm.sfx)` and `SubCover` get an exception for a list of
  moved-aside names whose claims the invariant holds (a ghost list, like `Wn`).

## Session log (branch `wal-c-create`, 2026-11-14)

*Setup*: base `origin/wal-create25` (`4004d7adef`); the `wal-above` build copied; every importer of the
changed modules rebuilt (281 modules: `Create`, the WAL `Link`, the tester's leaves) with no error.

**Done: design P's first stage** (commit `f1e467bdf3`; no axiom, no `sorry` added or removed; the TCB baseline
unchanged):
- `Handle.lean`: `walDirH`'s naming fact `nmd : Roots → Qp → IProp` (default `fun _ _ => walNamed dir`), its
  names fragment `nf` (default `none`); `walPipeH`'s pin `pp : Roots → DFrac → Prop` (default `True`, the pure
  conjunct `⌜n ≤ k ∧ pp R dq⌝`); `walHandleIn` passes `nmd nf pp`, `walHandleC` (`CloseHandle.lean`) `nmd nf`.
  **`walOpenWFU P Mr w dir Rp qp`**: `nmd := ⌜R = Rp ∧ q = qp⌝`, `nf := some dir`, `pp := R = Rp ∧ dq = own qp`.
  Edits outside the unit's files for the defaults: `CutPipe` (two lines), `openAtIndex` (one), `WAL__Close`
  (`wp_syncC`'s new argument), `WAL__sync` (`specC`'s error arm).
- `HandleUnnamed.lean`: `walOpenWFU_intro` (pinned), `walDirH_split`, `walPipeH_mono`, `walHandleIn_split`
  (the names fragment out and another back, the naming fact along a wand, the pin weakened),
  **`walOpenWFU_seal`** (the fragment `some dir` out; with `none` and `walNamed dir`, `walOpenWF`);
  `walOpenWF_unnamed`, `walHandleIn_nmd`, `walDirH_nmd`, `walOpenWFU_named` removed (no user left);
  `walOpenWF_unlocked_excl` proved directly.
- `Ghost.lean`: `walUnlockedTokX` (the free token less its names fragment), `walUnlockedTokX_join`,
  `walLockedTok_unlockX`; `Parked.lean`: `walParked_unlockX`; `OpenUnpin.lean`: **`walInvBody_unpinX`** (the
  put-back keeping the holder's names fragment), `walInvBody_unpin` now its corollary (statement unchanged);
  `CloseLawU.lean`: `walCloseLawU` takes no names fragment and returns `walUnlockedTokX`.
- Specs (internal; ledger 2026-11-14, "`Create`'s name registered only at success"): **`WAL.Close.specU`**
  (success: `w.dir ↦ dir ∗ walUnlockedTokX ∗ walNamesFrag (some dir) ∗ osCallPerm ½ ∗ ∃ j, osPathS Rp dir (own
  qp) j ∗ osPathS Rp dir (own qp) j`; error: `walLockedTok ∗ walNamesFrag (some dir)`), proved;
  **`WAL.sync.specC`**'s error arm returns `walNamesFrag nf`, proved; **`renameWALPost`**'s arm 2 `∃ x qd, ⌜dq =
  own qd⌝ ∗ UH x ∗ walOpenWFU P Mr w' dir R qd ∗ …`.
- `Create`: `createUH … qh x` keeps `Create`'s whole remainder `c` with `qh + (qh + c) = ½` and the split record
  `Wn`; `create_ghost` no longer registers; `create_handleIn` builds the pinned pending handle; the success exit
  (`create_named_cont`), after the parent's close and the deferred `RemoveAll`, names (`walInv_named`, moved
  after the close as the twenty-seventh session found it must be), registers (`walInv_register` with the whole
  `c`) and seals. `wal.Create.wp_proof` builds; its three cleanup `sorry` sites are unchanged, but each now holds
  everything P promised: the pinned pending handle and `createUH` with `qh + (qh + c) = ½`.

**`WAL.renameWALUnlock.spec`** (in the path: it is `renameWAL`'s hypothesis for arm 2). Still false/unprovable
as stated; its arm 2 is now the pinned pending handle, what design P needs. What a proof needs, unchanged by P
(ledger entries "unprovable as stated" and "(2) Create-specific"): (a) an `Open`/`ReadAll` variant over the
pending WAL with no client atomic update (`Open.spec` asks for one on `walDirIs dir`, which `Create` no longer
has after its commit), building the handle from `Create`'s claim fraction and returning it pinned; (b) a
`RenameWALOk` law from `U (some x) ∗ SpR x` to `UH x` and the reopen's resources; (c) a public `os.Rename`
spec for an absent source (the second rename after a first that took effect). None is a client-facing change.

**Second session part (same branch, after the coordinator's merge of `6a6ca38e90` into `wal-int`).**
- **Step 1 done** (commit `9acff93374`): the tail lock file. `walHandleIn`/`walHandleC`'s naming fact takes the
  tail's `*os.File` (`nmd : Loc → Roots → Qp → IProp`, passed as `nmd f` to `walDirH`, whose type is unchanged);
  `walOpenWFU P Mr w dir Rp qp tf` pins it (`Create`'s `f`); **`Close.specU`** returns it closed (`os.ownFile tf
  (-1) _`) on success, open with its fd on the sync's failure. The tail writer's failure predicate **`tailWB`**
  (`TailWriterW.lean`) keeps the tail's file and fd: `wp_tailWriteAtW`/`wp_tailWriteW`'s error arms return
  `osFd` (they held it), `wal.tailWriterW`'s `B` is `tailWB` (`encoder__encodeTail` follows), `sync.wp_core`'s
  error arm returns the file and fd (flush failure: `tailWB`; fdatasync failure: from `walTailW`), **`sync.specC`**'s
  error arm with the naming fact at them. **`renameWALPost`'s arm 2** now also returns the caller's segment file
  (`walLockLeft f …`: the retry's `w.Close()` closed it, or left it open), the reopened tail `tf` unknown. Gotcha:
  a lambda naming fact passed through a metavariable (`wp_syncC … _ _`) is beta-reduced by `instantiateMVars`
  and no longer matches the unfolded `(fun … ) f` in the context; pass it explicitly (`WAL__Close`,
  `WAL__CloseU`).
- `origin/wal-int` (`87ead66a41`, with this branch) merged (`9750299bba`, clean); `Create` and the 24 importer
  leaves of every changed file (the WAL `Link`, `BootCrash`, the tester, `durable.Crash`) build.

**Left (the next steps, in order):**
1. ~~**The tail lock file after the cleanup.**~~ (done above; the original note:) `Create`'s deferred `f.Close()` runs after `cleanupWAL` (`retErr`
   set): `Create` needs `os.ownFile f (-1)` (after `Close.specU`'s success: `os.File.Close.specClosed`) or the
   open file (after its failure). `walOpenWFU` hides the tail lock: pin it too (a fourth pinned value: the
   handle's last lock `lt` and its `*os.File`), and `Close.specU` returns the file (closed, or open with its
   `osFd` when the sync failed: `sync.specC`'s error arm then returns the tail's `os.ownFile`/`osFd`, which
   `wp_core`'s flush error arms must keep; twenty-fifth session's obligations (1)-(3)). The pin needs a new
   defaulted parameter of `walHandleIn` (its existentials `lt f`); every pure conjunct is destructured by
   position in several modules, so the cheapest place is another function-valued parameter like `nmd`.
2. **`cleanupWAL`'s spec and proof** (`LinuxFs/Spec/.../wal/WAL__cleanupWAL.lean`), `Create`-specific, over a
   caller law for the rename: pre the pinned pending handle, its purge right, `osCallPerm ½`, the area's path,
   a frame `Pre`, and a law `∀ s, (s's characters timestamp ones) → Pre ∗ walUnlockedTokX ∗ walNamesFrag (some
   dir) ∗ the two paths ∗ notCrashed ={⊤}=∗ notCrashed ∗ ∃ N h J q r lb Qr, ⌜nm, brokenName nm s ∈ N, nm holds
   J, q + r = 1⌝ ∗ osNames jr N (own q) h ∗ osLogLb lb ∗ osAUnc (osNames jr N (own r) h) (renDirOutA jr J N nm
   (brokenName nm s) h (own r) lb) Qr ∗ (∀ err, the rename's post -∗ osCallPerm 1 -∗ … ={⊤}=∗ Fin err)`; post
   the area's path and `(⌜err ≠ nil⌝ ∗ walLockedTok ∗ walNamesFrag (some dir) ∗ osCallPerm ½ ∗ Pre) ∨ Fin err`.
   Callees: `Close.specU`, `time.Now`, `time.Time.Format.specBroken`, `fmt.SprintfBroken.spec`,
   `os.Rename.specDirAnySnc`, zap. Plus `fmt.ErrorfAny.spec` in `Create` for the deferred closure's
   `fmt.Errorf("%w (after: %v)", …)`.
3. **`Create`'s three sites** over it: the `Close`-failed arm registers `nm` (`walInv_register`, any fraction)
   and merges back (`create_areaBack`, `T := walLockedTok`), as arm 4 does; the law: `c + qp + qp = ½` from the
   two paths (`os.osPathS_unchild` twice, `osNames_agree` for `J`), the broken name split off the area claim
   (`walInv_drop`, as `nm.tmp`), the claim on `[nm, brokenName nm s]` merged, the invariant's half's `osAUnc`;
   the rename failed: register and merge back; the rename took effect: **the moved-aside step** above
   (`WalsAt`'s exception holding `Create`'s names fragment, the moved-aside list in `walAreaRes`), the one
   remaining invariant design.

## Session 3 (branch `wal-c-create`, 2026-11-14/15): `cleanupWAL`, the three sites; the rename blocked on the invariant

*Setup*: base `origin/wal-c-create` (`408d79f071`, = `wal-int`); the previous session's worktree build copied
(same commit). The previous session's worktree still holds the local branch `wal-c-create`, so this one works
on a local `wal-c-create-b` pushed to `origin/wal-c-create`.

**Proved** (no axiom; the WAL's `sorry`s go from one, `wal.Create.wp_proof`, to two smaller ones in
`CreateCleanup.lean`; `etc/tcb-baseline.txt` and `etc/tcb-collections/wal-fsext.txt` edited by hand to match,
to be confirmed by `etc/tcb-report.py --check --update` at integration):
- **`WAL.cleanupWAL.spec`** (new, internal, `Create`-specific: `LinuxFs/Spec/.../wal/WAL__cleanupWAL.lean`) and
  **`WAL.cleanupWAL.wp_proof`** (`LinuxFs/Proof/.../wal/WAL__cleanupWAL.lean`, `lake build` clean). Pre: the
  handle before naming `walOpenWFU P Mr w (child r nm) Rp qp tf`, its purge right, the caller's half of the call
  permission, a frame `Fr`, and the rename's law `cleanupLaw` (at the timestamp `ts`: from `Fr`, what a
  successful `Close` returned and `notCrashed`, the precondition of `os.Rename.specDirAnySnc` of `r/nm` onto
  `r/nm.broken.<ts>`, and a continuation from its post to `Fin err`). Post: `Close` failed in its sync
  (`walLockedTok`, the names fragment, the tail file open, `Fr`); `Close` returned everything but an error
  (`walUnlockedTokX`, the names fragment, the paths, the tail file closed, `Fr`); or `Fin err`. Callees:
  `Close.specU`, `time.Now`, `time.Time.Format.specBroken` and `fmt.SprintfBroken.spec` (the two pending
  hypotheses, now reaching `wal.wp_Create` in the Link), `os.Rename.specDirAnySnc`, zap.
- **`Create`'s three sites** (`create_cleanup`, called by `create_named_cont` at the parent's `OpenDir`, `Fsync`
  and `dirCloser` failures, in both arms 1 and 2): the logs, the deferred `cleanupWAL` over `createFr` (the area
  path, the area claim less `nm.tmp` and `nm`, `Create`'s fraction `c` of `nm`'s claim, the tagged claims, the
  split names) and `create_cleanupLaw`; `fmt.Errorf("%w (after: %v)")` of its error (`fmt.ErrorfAny.spec`); the
  deferred `f.Close()` (arm 1: the tail lock's file, open after a failed sync, closed after `Close`; arm 2: the
  caller's segment file `walLockLeft`, `Hll2`); `RemoveAll(nm.tmp)`. **The two outcomes without a rename are
  proved**: the name registered (`walInv_register`, `Create`'s `c`) and `nm.tmp` merged back (`create_areaBack`,
  `T := walLockedTok` after a failed sync, `walUnlockedTokX` otherwise, `walUnlockedTokX_unlocked_excl`), as arm 4.
  The outcome with a rename goes through `createFin` and `create_cleanBack`. `wal.Create.wp_proof` takes two new
  hypotheses, `cleanupWAL.spec` and `fmt.ErrorfAny.spec`, both proved and linked (`Link.lean` regenerated, builds).
  Arm 2's handle's fraction is `Create`'s `d` (`hqd`).
- The Fsync site's comment now says the fork's fix (the parent closed without `dirCloser`) is in the translation.

**Left: `create_cleanupLaw` and `create_cleanBack` (`CreateCleanup.lean`, `sorry`)**: the rename's law. Its plan
(sound up to the update): `c + d + d = ½` from the two pinned paths (`os.osPathS_unchild` twice, `osNames_agree`,
`osNames_frac`); `nm`'s claim merged back into the area claim (`walInv_merge2`, `T := walUnlockedTokX`) so the
rename's claim is `N.diff [nm.tmp]` (holding `nm` and the broken name, `AreaOk`'s `nm.<sfx>`); `lb := h'.next`
(`osNames_next`); the update with the program's half split (a quarter to the rename, a quarter in the update's
resource) so that an unused update gives it back (`osAUnc_none`, as `renameWAL` does). **Two findings block it,
both invariant changes, not made** (they touch `walInvBody` or its conjuncts, which four other units' proofs
destructure; the coordinator should decide where they land):

1. **The update cannot find the invariant's half of the area claim.** `osAUnc`'s opening runs inside the `os`
   step with the shared invariant's namespace open (`osAuMask` excludes `osShN`), so `osClaims_keys` (how the
   program's steps find the invariant's half of an area claim from their own) is unavailable there; and nothing
   in the invariant pins the area claim (`Create`'s commit found its claim through the creating map:
   `CreatingOk` gives `(jr, N, h) ∈ cl` for an entry; an unpinned claim's invariant half could in principle have
   moved, and `osNames_agree` gives the history only once a claim of the same names is found). This blocks even
   the outcomes where the rename has no effect. Options: (a) a pin in the invariant for "the claim the program
   renames in", e.g. a creating-map entry kind for the cleanup (`CreatingOk` of an entry `J = jr`-marked, or a sum
   type) recorded by an invariant step at the merge, where `osShN` is available; (b) a new ghost map
   claim-key -> history in `walInvBody` with its fragment in the update's resource; (c) do the rename on a claim
   the invariant already pins. Recommendation: (a), recorded by the merge step (`walInvBody_merge2`'s variant),
   removed by the commit or abort.
2. **The moved-aside step** (a rename that took effect; the plan above) needs, beyond the session-1 list
   (`WalsAt`'s exception for the moved WAL's name, `walAreaRes`'s for the broken name, whose directory's claims
   are the invariant's): **the pending WAL known unnamed in the invariant.** After the rename a crash may keep it
   (`nm` absent), which `CrashTo` allows only for `named = false`; `named` is monotone (`walDurLe`) and
   `walInvBody_named`/`walInvBody_namedBy` need only a claim fraction holding `nm`, so nothing now excludes that the
   real WAL got named before the cleanup. Proposed: `walNamesRes` (or `walInvBody`) records `o = some dir → the
   WAL in dir is unnamed`; `Create`'s success exit registers before naming (now: names, then registers);
   `walInv_namedBy` (`ReadAll`) gets `o ≠ some dir` from its handle's `walNamesFrag none`.
   Minimal forms found for the other two: `WalsAt`'s second part weakened to `h.cur !! lay.nm = some (.dir lay.j) ∨
   h.cur !! lay.nm = none` (every preservation lemma carries it; its two strong users, the registration's
   `nameShare` and `names_split_start`, can take the strong fact from their own claim and from `walsAt_start`;
   `walDirAt_pure`'s second part has no user); `AreaOk`/`walAreaRes`'s `SubCover` exempting a broken name
   (`∃ nm s, walNameOk nm ∧ b = brokenName nm s`; its one user, `area_takeTmp`, refutes it for `nm.tmp`).
   With the merge approach the moved step is one claim replaced by its logged self in `cl`; `CreateCommit.lean`'s
   lemmas (`regionCrashedK_create_keep/drop`, `treeUnren`, `crashOkW_create_other`) are generic in the names but
   assume the target absent (the cleanup's target may hold an empty directory, `RenTgtOk`): variants needed.

**Next step**: the coordinator's decision on 1 and 2 (where the invariant changes land); then the law (the merge,
the pinned update, its no-effect commit, the moved-aside commit) and `create_cleanBack` (`createAreaL` to carry
`h'`'s pure facts: as `h` off `nm.tmp`/WAL names, or moved). `renameWALUnlock` not attempted.
