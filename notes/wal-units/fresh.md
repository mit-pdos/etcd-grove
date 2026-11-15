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
becomes `∀ W : WalGS GF, …`. A linked result is generic in its section's `[W : WalGS GF]`, so it is used only
for the specs the tester takes under `∀ W`; the others (`walpb` getters, `durable`) are re-linked from their
proofs. 96 results. Collection `etc/tcb-collections/wal-tester.txt` (its baseline lines not written:
`etc/tcb-report.py` refuses to run until every root module of the repository is built, ~760 modules stale in
this worktree; run `--collection etc/tcb-collections/wal-tester.txt --check --update` at integration).

Linking the tester for the first time imported its modules together, which showed name clashes (each pair
had never met in one importer): `tU64_length`, `tHsBytes_length` (identical in `DecRep` and `OrLen`: moved to
`Defs.lean`), `tOpBytes_length` and `tEntBytes_length` (different statements: `DecRep`'s renamed `…_ge`,
`decoder__ops` follows), `candsElems_snoc` (identical in `DecRep` and `CandsLemmas`: `DecRep` imports
`CandsLemmas`), `tSaveSnap_ents_sub` (different: `walFold`'s renamed `tSaveSnap_ents_mem`), and the WAL's
`walGhost_named` (`NamedView`'s, the tester session's, renamed `walGhost_raiseNamed`; `CutAuLemmas` has the
other).

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

**Trust base** (`#print axioms` of `walTester.etcd_wal.wp_Main`, `lake env lean`; `etc/tcb-report.py` could
not run, above): no `sorryAx`. Besides Lean's three and 1168 generated type axioms (`zero_val`/`underlying` of
the translations' axiomatized types), the axioms are the WAL's (as `wal-fsext.txt`: `binary.ReadInt64LE`,
`fmt.SprintfWalName`, `fmt.SscanfWalName`, `io.ReadFull`, `pbRecordC_reg`, `pbSnapC_reg`, `proto.ClonePb`,
`proto.MarshalAppendCachedRecord`, `proto.MarshalPb`, `proto.SizePb`, `proto.UnmarshalPb`, `recEncC_ok`,
`snapEncC_ok`, `strings.HasSuffix`, `time.Duration.Seconds(_ptr)`, the `zap` ones), Perennial's
`errors.As.wp_proof` and `time.Now.wp_proof`, the tester's `entryEncC_ok`, and nine `_native.bv_decide`
auxiliary axioms of the tester's `tSaltOf_tEntData` and `u64Acc_step` (`bv_decide`'s native-code
certificates: they trust the compiler; replacing them by `bv_decide`'s kernel mode, or `decide`, would drop
them). `wal.wp_Create`/`wp_CreateFresh`: the WAL's list, no `sorryAx`.

## Decisions left for the user / coordinator

- Strengthen `wal.Exist.spec`'s `false` arm to `o = none` (proved already; closes specgap P6; `Boot` then
  uses `Create.spec` at `Pv o := o = none` or keeps `specFresh`). Recommended.
- The closed theorem (not stated: the user's hard stop).
