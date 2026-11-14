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

## Session log

(below)
