# Unit `fresh`: `wal.Create.specFresh` proved; the tester's `Link.lean` (branch `wal-c-fresh`, base `wal-int`, 2026-11-15)

The coordinator chose option (a) of the tester's B3 (`notes/wal-units/tester.md`, eleventh session):
prove `Create.specFresh` in the WAL layer.

## The finding: no invariant change was needed

The plan expected `Create` to have to replace an unnamed, empty WAL whose directory is not at its name
(the moved-aside one, or a crash survivor). That state never meets `Create`'s commit:

- **`Exist`'s `false` already means no WAL in the real state** (`wal.Exist.wp_core`'s post: `b = false →
  od = none`, `od` the real `s.wal !! dir`). With the lock token held, no registration is pending
  (`walNamesFrag none`), so every present WAL's name is registered (`walNamesRes`) and `Exist` reads its
  directory through the registered claim, finding its segment (`WalAbsD.nonempty`, `WalsNamed`): `true`.
  A WAL moved aside by `Create`'s cleanup leaves the pending registration `some dir` forever
  (`notes/wal-units/create.md`, session 4), so the lock token, which `Exist` and `Create` need, cannot be
  formed again in that generation; after a crash a surviving unnamed WAL is a registered WAL of the new
  generation, its directory at its name (`walInv_crash`'s start), so `Exist` answers `true`.
- So `Exist`'s spec's `false` arm, `wal.ExistFalseOk o` (none, or a fresh unnamed WAL), is weaker than
  what is proved: `existFalseOk_of_le` only ever produces its left disjunct, `o = none` (the client's
  view is below the real state). specgap P6 ("`Exist` false does not give `walAbsent`") is a spec gap,
  not a gap in the code or the invariant. **Not changed here** (it would touch `Boot`, the tester's): the
  `false` arm can be strengthened to `o = none`, after which a client gets `walAbsent dir` from `Exist`
  directly. Recommended to the coordinator (it also closes specgap P6 for the server's
  `bootstrapNewWAL`).

What `Create` lacked was only the *route* of that fact: it called `Exist` through `specCreate`, which
returned nothing, and read the absence off its client's `walAbsent` update (`walInv_absent`), at its start
and again at the commit. Now the absence comes from `Exist` and from the lock token, and the update may
start from any view.

## What changed

**Specs** (ledger 2026-11-15, "`wal.Create.spec` generalized: the update from any view"):
- **`wal.Create.spec`** (`LinuxFs/Spec/.../wal/Create.lean`): a new binder `Pv : Option WalDur → Prop`
  after `Q`; the update `AU <{ ∃∃ o, walDirIs dir o ∗ ⌜Pv o⌝ }> … <{ walDiskAt dir (walDurFresh md), COMM
  Q }>`, in the precondition and in the error arm that commits nothing. Strictly stronger than both the
  old spec (`Pv o := o = none`, up to the update's form) and `specFresh`.
- **`wal.Create.specFresh`** (`CreateFresh.lean`): statement unchanged; no longer a hypothesis.
  **Proved**: `wal.Create.wp_specFresh` (`LinuxFs/Proof/.../wal/CreateFresh.lean`, new), `Create.spec` at
  `Pv := wal.ExistFalseOk`. Linked: `walfs.wal.wp_CreateFresh` (WAL `Link.lean`, regenerated: 213 results).
- **`wal.Exist.specCreate`** (internal, `CreateCallees.lean`): on `false`, `walAreaResFree jr nm` in place
  of `walAreaRes jr`.

**Vocabulary**: `WalFs.walAreaResFree jr nm` (`CreateFree.lean`, new): `walAreaRes` with `nm` in the
program's area claim, nothing there (`h.cur !! nm = none`), and not registered (`nm ∉ Wn`);
`walAreaResFree_res`.

**Proofs**:
- `walInvBody_existPin`, `walInv_existStart` (`ExistPin.lean`): the no-WAL case also gives `nm ∉ Wn`
  (`split_absent`, already there). `wal.Exist.wp_core`: its post `(⌜b = true⌝ ∗ walAreaRes jr) ∨ (⌜b =
  false⌝ ∗ walAreaResFree jr nm)` (the `ReadDir` error arm: `ENOENT` gives `false`, another error `true`);
  `wp_proof`, `wp_specCreate` adapted.
- `walCreating_absent` (`CreateAu.lean`, new): while the creating entry of `dir` exists, the invariant
  holds the free lock token (`walCreatingAuth`'s create kind), so `o = none` in `walNamesRes`; with the
  program's `walSplitFrag Wn` and `nm ∉ Wn`, `split_present` gives `s.wal !! dir = none`.
- `walCreateP`/`walCreateQ` (`CreateAu.lean`) take `Pv` and `Wn`; `walCreateP` holds the client's
  `Pv`-update and `walSplitFrag Wn` (returned by the commit's `some` arm too). `walCreate_osAUnc` takes
  `hnW : nm ∉ Wn` and finds the absence by `walCreating_absent` (no longer from the update).
  `createFresh_osAUnc`, `createU`, `createU_none`, `create_spine` (`CreateRename.lean`), `create_ghost`
  (`CreateHandle.lean`: `Wn`'s fragment now from `createU`, not a separate argument) follow.
- `wal.Create.wp_proof`: `Pv`; after `Exist`, opens `walAreaResFree` (in place of `walAreaRes_open` and
  `walInv_absent`); the fragment goes into `walCreateP`; the arms take it back (arm 3 from `walCreateP`,
  arm 4 from `walCreateQ`). The spine law's `grind` moved into a top-level lemma, `create_qp_twice`: with
  the new hypotheses in context, `grind` inside the proof produced a term the kernel rejected
  (`eq_false_of_decide` on a byte literal), the known gotcha.
- `walInv_absent` (`CreateAbsent.lean`) has no user left; kept (no file moves in this unit).

No axiom, no `sorry`, no change to `Inv.lean`, the lock threading, or the fds of `Create`.

## The tester's `Link.lean`

`etc/gen-link.py --wal-tester` (`etc/link_walfs.py`'s `TESTER`): the tester's proofs
(`LinuxFs/Proof/.../examples/etcd/wal/`) linked, the WAL's and `durable`'s results taken from their
`Link.lean`s as they are (not re-linked; their hypotheses become the caller's). A binder `∀ W : WalGS GF,
S (W := W) …` is given `fun W : WalGS GF => …`, and a hypothesis reached through it that mentions `W`
becomes `∀ W : WalGS GF, …`. 65 results, 53 closed. Collection `etc/tcb-collections/wal-tester.txt`.

`etcd_wal.wp_Main`'s hypotheses (the leftover specs and premises):
- the client's protobuf laws on `walRaftP`/`walRaftMr` (`WalPbIn.*Law`: CloneHs, GetIndex, GetTerm,
  IsEmpty, MarshalEnt, MarshalHs, MustSync, Nil, UnmarshalEnt, Zero) and on the unmarshaller `U`
  (`U.Ok walRaftMr`, `U.SnapCoh`, `WalHsOwn`), `WalDecEnvSupply`;
- Perennial-gap specs: `errors.AsLinkError`, `errors.IsErrno`, `errors.IsPathErrnoEof`,
  `errors.IsPathErrnoNotExist`, `errors.IsPathErrnoTerm`, `filepathlite.IsAbs`, `fmt.ErrorfErrsNot`,
  `fmt.ErrorfErrsTerm`, `fmt.SprintfBroken`, `time.Time.Format.specBroken`, `io.CopyFiles`,
  `proto.UnmarshalWalRecordE`, `zap.NewNop`;
- the WAL's open ones, at every generation (`∀ W`): `WAL.renameWALUnlock.spec` (false as stated,
  `create.md`), `WAL.Close.specFailed`.
- `wp_Main` is generic in a second `P U HsO` (`h_WalHsOwn : WalHsOwn P U HsO`, beside the one at
  `walRaftP`): `ValidSnapshotEntries`' result is generic in a model its spec does not fix
  (`validSnapshotEntries.specPinned`'s), so the link keeps it a parameter; instantiate `P := walRaftP`.

The trust-base report: see the end of this file.

## Decisions left for the user / coordinator

- Strengthen `wal.Exist.spec`'s `false` arm to `o = none` (proved already; closes specgap P6; `Boot` then
  uses `Create.spec` at `Pv o := o = none` or keeps `specFresh`). Recommended.
- The closed theorem (not stated: the user's hard stop).
