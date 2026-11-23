# A state-determined interpretation for the file extension's tree (design, 2026-11-23)

Upamanyu's principle: "The ghost state inside of the state interp should just be determined from the
state. I don't see why there'd be a need to do any ghost updates there." This note is a design only,
with no code. It is written against `lean` `f85bfe0827`, with kvnet-proof already merged. Decided on
etcd-grove #15 (kaashoek agreed, 2026-11-23) and on perennial#683, which lands part 1 only.

## 1. Today

`osCtx` (`GooseLang/Ext/Fs/Ghost.lean:1401`) is `osCtxF ∗ treeCtx ∗ ofdCtx ∗ lockCtx`. Its tree part
`treeCtx hL st := (treeLegacy hL st ∨ treeShared hL st) ∗ commitRes hL st` (`Ghost.lean:1263`) is a
**mode**: which disjunct holds is not a function of `st`. In detail:

- **The disjunction itself** (`:1263`). Nothing in `st` says which mode a generation is in.
- **`legacyHolds`** (`:1138`), inside `treeLegacy` (`:1242`): the authorities of the shared names
  (`γs γdfS γcS γperm γn γlen γlog γg`, `OsGS` at `:643-660`), all **empty**, whatever `st` is.
  This is why no shared resource can exist in legacy mode.
- **`treeShared`** (`:1252`) holds three things that `st` does not determine. The legacy history is
  frozen at `V0`: `gAuth γd (histMap (roots, V0))`, and the interpretation keeps the whole fragment
  `gElem γd () 1 (roots, V0)` itself. The switch point `s0`, the legacy prefix that `TreeCohS`
  exempts (`:1225`), is also ghost. And `γdf`/`γc` are kept empty.
- **Off-step updates of the interpretation** that move between these states:
  - `treeCtx_switchG` (`TreeSharedKit.lean:88`) fills `legacyHolds`' auths and freezes `γd`.
  - `osShare_ctx`, `wp_osShareE`, `wp_osShareE_upd` (`TreeSharedSwitchE.lean:36,110,170`) and
    `wp_osShareE_acc` (`TreeSharedKit.lean:186`) are the same switch, reached by `wp_ext_acc` before
    a step.
  - `wp_osShare'` (`TreeSharedSwitch.lean:311`) does it at a `CallBegin`.
  - `os_local_crash`'s shared branch (`CrashTok.lean:410`) rewrites the old `γd` at the crash.
  - `crashMode`/`crashShared` (`CrashTok.lean:178,189`) carry the mode into the crash rest.
- **Not modes, and not addressed here:** the per-call and per-fd annotations (call fractions in `Γc`,
  logging vs guard calls `Γg`, `DirPh` views) and the files' refinements in `osCtxF` (`OsMeta`'s
  ghost fields, `CandRel` cuts). They change only in step proofs, at the step that creates them. Every
  other `wp_ext_acc` user (`TreeSharedRoots.lean:69`, `wal/MetaZf.lean:36`, `WpPostShared.lean:71`)
  only reads and restores the interpretation. `commitRes`'s `∃ c` is ghost too, but it can be made
  `c := committed prefix of st` at no cost (optional, stage 5).

**Why there are two modes** (`notes/wal-fsext-i2-design.md` §0.2, §2.1):
- *Legacy* is the whole-history logic: `osTree dq R V` (`World.lean:168`) is a fraction of `γd`,
  calls and dir fds hold fractions of it, the log is `Sequential`, and a crash gives a prefix
  (`crashRest_tree`, `CrashTok.lean:346`). walfs, crashlog, bboltfs and `Proof/os/{Ns,OpenFile,Crash*}`
  use it.
- *Shared* is for concurrent path calls (the WAL). It has name claims `osNames` under the invariant
  `osSharedInv R` (`TreeSharedRes.lean:228`), call permissions `osCallPerm`, and a crash that keeps a
  closed cut (`crashRest_region'`, `TreeSharedCrash.lean:94`).
- Mutual exclusion is by ghost validity. The shared invariant holds `γs` whole, and in legacy mode
  `γs`'s auth is `∅` (`sharedInv_legacy_excl`, `:82`). The shared interpretation holds `γd` whole.

**What the crash frame needs.** A generation's crash frame is fixed when its obligation returns
`WP ∗ frame`. The WAL's frame (`tester_crash`, kvnet's `kvGen_crash`) must already own `osSharedInv`
and the client invariants that hold claims, because a crash can come before the first step. So the
switch has to happen before the WP, and today it needs the interpretation. Hence `CrashAdequacyAcc.lean`
(`goose_crash_adequacy_acc`, `:225`), `AdequacyShared.lean:41`, and kvnet's `TopBridge.lean`
(`CrashBootWpG`, the shape of perennial#683 part 2). `TopCrash.lean` handles the other choice: a
crash in the window before a first-step switch.

## 2. Proposed design

**The interpretation keeps one shape, with no mode.** `γd` and `γs` merge into one name `γH`:

```
treeCtx hL st := ∃ Γdf Γc ΓdfS ΓcS Γg s0,
  ⌜FsTreeWf st ∧ TreeCohL st Γdf Γc ∧ TreeCohS st s0 ΓdfS ΓcS Γg ∧ Part st Γdf ΓdfS Γc ΓcS Γg⌝ ∗
  gAuth γH (histMap (st.fs.roots, (st.fs.treeDur, st.fs.metaLog))) ∗       -- a function of st
  gAuth γdf Γdf ∗ gAuth γc Γc ∗ rdRes Γdf ∗ callRes Γc ∗                     -- legacy records
  gAuth γdfS ΓdfS ∗ gAuth γcS ΓcS ∗ callResS ΓcS ∗ gAuth γg Γg ∗ callResS Γg ∗ commitRes st
```

- `Part` says that each of `st`'s dir fds and calls is in exactly one family. `TreeCohL` is today's
  `TreeCoh` minus `hist` and `seq`.
- `s0` is a pure witness, not ghost state.
- `γn`, `γlen` and `γlog` leave the interpretation entirely. Their auths were only ever `∅` there.

**The whole tree carries both views.** `osTree` keeps its name, its signature and its laws
(fractional, agreement, timeless). Its body becomes:

```
osTree dq R V := gElem γH () dq (R, V) ∗ ⌜Sequential V.2⌝ ∗ osCallPerms_dq R ∗ osKit_dq R V
osKit_dq R V := ghostMapAuth γn dq (claimsInit V (dirsOf V)) ∗ [∗ j ∈ dirsOf V] osNames j (.except []) dq _
              ∗ monoNatAuth γlen dq |V.2| ∗ ghostMapAuth γlog dq (logMap V.2)
```

- `os_local_init` allocates these names already filled in, and `osStart`/`treeStart` hands out
  `osTree 1 R (treeDur, [])` as today. So `fs_start`, `fs_crash_adequacy` and `fsStartRes` keep their
  text. `legacyHolds` disappears.
- `callRes`/`rdRes` hold `osTree`-shaped fractions. A legacy logging step re-initialises the kit to
  the new `V`, using ghost state it holds whole (`osTree_relog`, a proof-side `==∗`).

**The legacy view** is `osTree` held directly. The legacy specs keep their statements.

**The shared view** comes from a proof-side allocation, a plain fancy update that never touches the
interpretation:

```
osShare R V : osTree 1 R V ={E}=∗ osShared R V     -- osSwitchKit_open, with γH ◯1 put in osSharedInv
```

`osSharedInv` holds `gElem γH () 1 (R, Vs)` where it now holds `γs`. Exclusion still comes from
validity, now with no help from the interpretation:
- A shared logging step opens the invariant and gets `γH ◯1`. So no legacy record exists
  (`whole_aloneG`, `TreeSharedKit.lean:53`).
- A legacy logging step holds `osTree 1`, so it holds every call permission whole. So no shared or
  guard call is in flight (their `callResS` hold fractions). The step re-establishes `TreeCohS` at
  `s0 := |log|`, from `osTree`'s `Sequential`, as `cohS_switch` does (`TreeSharedSwitch.lean:115`).
- A non-logging step of one family leaves the other's coherence alone (`TreeCohS.congr` and its
  legacy twin). Shared dir fds hold nothing, and `PhOkS` survives any entry.

**The crash.** `TreeCohS` now always holds, so `os_local_crash` takes one branch. It uses
`osCrash_relS` (`CrashFiles.lean:148`) and allocates the new generation fresh by `os_local_init st'`,
as now. It updates nothing:
- `crashRest` keeps the old `γH` authority, which is the crashed state's history, and the closed-cut
  facts. `crashMode` and `crashShared` go.
- `treeLeft` holds the new `osTree' 1 R V'`, kit included.
- `crashRest_region'`, `crashRest_treeS'` and `crashRest_treeWf'` keep their statements. Their proofs
  lose the legacy case.
- `crashRest_tree` keeps its statement. It gets `TreeCrashed W V'` from the cut and the `Sequential
  W.2` of the old `osTree` it is given (a new pure lemma, §5).

A crash frame then gets what it needs with no update: the old `osSharedInv` is persistent and already
in the frame, and the new generation's tree and kit arrive through `crashStart`. The next generation's
obligation runs `osShare` itself before its WP. So that obligation never needs the interpretation, and
plain Perennial adequacy suffices.

## 3. Per-client impact

No trusted part changes: `Impl.lean`, `Tree.lean`, `Paths.lean`, `Premises.lean` and Perennial's
adequacy theorems stay as they are. Only the untrusted `fs_interp`/`fs_crash_interp` and the proof-side
vocabulary change. No top-level statement changes, except kvnet's, which gets stronger (it loses a
hypothesis).

| Client | What changes | Size |
|---|---|---|
| `Ext/Fs` core | `Ghost.lean` (`treeCtx`, `os_local_init`, `osStart`), `World.lean` (`osTree`, laws, legacy steps' `osTree_relog`), `CrashTok.lean` (single-branch `os_local_crash`, `crashRest`), new Seq+cut→`TreeCrashed` lemma, ~20 `TreeShared*.lean` step proofs (`γs`→`γH`, `Part`, legacy branch dropped), `TreeSpecs*`; delete `TreeSharedKit`'s G-half, `CrashAdequacyAcc.lean` (268); `AdequacyShared` re-proved over `fsSQ_crash_adequacy`, statement kept | +1.2k / −1.0k, ~1.5 agent-weeks |
| bboltfs, crashlog, walfs (incl. `Boot`, `DSBase`), `Proof/os/{CrashOps,CrashFile}` | none in statements; three `unfold osTree` become `osTree_agree`/`osTree_timeless` | ~15 lines |
| `Proof/os/PathKindS.lean` | the legacy-exclusion branch goes (`:93-101`, `:168-176`) | −20 |
| WAL proofs (`Proof/go_etcd_io/etcd/server/v3/storage/wal/*`) | none: `osShared`, `osNames`, `crashRest_region'/treeS'/treeWf'` keep their statements | 0-30 |
| WalTester | none: `fsSQ_crash_adequacyShared` keeps its statement, only its proof changes | 0 |
| `etcdstart/WalAreas`, `runtime/StartFiles` | `wp_osShareE` kept as a 3-line wrapper over `osShare`, or call `osShare` directly | 0-20 |
| kvnet (`TopBoot`, `ReplicaLinked`, `TopBridge`, `TopLevelRobustness`, `TopCrash`) | `kvGen_boot` drops its `localCtx σ` argument and uses `osShare`; `kvRep_gen` proves `CrashBootWp` (with `£ 1`) instead of `CrashBootWpG`; delete `TopBridge.lean` and `raft_kvnet_robust_of_errors`'s `Hb`; `TopCrash`'s pre-switch window becomes dead code (delete it) | −150 / +40 |
| `Net/Statement/NetFsBridge.lean` | `CrashBootWp`'s frame gains `£ 1 -∗`, from #683 part 1 | ~15 |
| osfs/netfs `Results`, bbolt `Results` | none | 0 |

## 4. Migration order (each stage lands alone, with the full build green)

0. **Perennial #683, part 1 only** (`£ 1` per crash), then the pin bump. Callers gain a `_`.
   `NetFsBridge`'s `robust_of_netFsBoot_addrs` passes the credit to `CrashBootWp`.
1. **The interpretation.** The new `treeCtx`, `osTree`, kit and `os_local_crash`, plus `osShare`.
   Every old switch lemma stays as a wrapper with its statement unchanged:
   - `wp_osShareE`, `wp_osShareE_acc` and `wp_osShare'`: `osShare` and the continuation.
   - `osShare_ctx`: frames `localCtx` untouched.
   - `treeCtx_switchG`: becomes an `==∗` that ignores `treeCtx`.

   No client file changes, apart from the `unfold osTree`s and `PathKindS`.
2. **Adequacy.** `AdequacyShared` re-proved over `fsSQ_crash_adequacy`, with the switch in the
   generation's obligation. Delete `CrashAdequacyAcc.lean`. WalTester needs no change.
3. **kvnet's first generation without part 2.** `Hstart` gets `fsStartRes`, that is `osTree 1`, which
   now contains the kit. The generation obligation `P L ⊢ threadTok ={⊤}=∗ WP ∗ frame` runs `osShare`
   and `durBoot` before the WP, so the frame owns `osSharedInv` and `kdFileInv` before any crash.
   Later generations do the same from `crashRest_treeS'`. Delete `TopBridge`/`Hb`. Needs stages 0 and 1.
4. **Cleanup.** Retire the wrappers (`osShare_ctx`, `wp_osShareE_upd`, `treeCtx_switchG`) and move
   their users to `osShare`.
5. **Optional.** `commitRes` with `c` determined by `st`. Legacy calls as shared calls holding every
   key, which would make one record family.

## 5. Risks and open questions

- **Allocating before a first crash without the interpretation: yes.** Everything `osShare` consumes
  is a fragment handed out at `local_init`/`local_crash` (`osTree 1` with its kit). The generation's
  obligation is a fancy update before `WP ∗ frame`, in Perennial's single-node and distributed
  theorems alike. The one requirement is that `os_local_init` fill the kit's auths, which today are
  `∅` in `legacyHolds`.
- **Credits at a crash.** `osSharedInv`'s body is timeless, so `crashRest_region'`/`treeS'` need no
  credit. Only client invariants whose bodies are not timeless need one (kvnet's `kdFileInvK`). That
  uses the single `£ 1`: strip all such laters in one `lc_fupd_elim_later` after opening them together.
  A future frame that must open invariants in sequence, under nested laters, would need more. Part 1's
  soundness argument allows any fixed number of credits per crash.
- **The new pure lemma** (`Closed S ∧ Sequential log ∧ slotAfter … → TreeCrashed`). It replaces
  `osCrash_rel`'s direct proof. Expected to be easy, since a closed set of a sequential log is a prefix.
  Fallback: `TreeCohS` keeps `Sequential (log.take s0)` and `crashRest` carries `osCrash_rel`'s fact
  for the prefix.
- **`Part` and the `TreeCohS` fields `cover`/`fds`.** These change from "mirrors all of `st`" to
  "mirrors its family". The change runs through every shared step proof. It is mechanical but the
  bulk of stage 1.
- **The perms inside `osTree`** are what exclude a legacy logging step while shared calls are in
  flight. Without them, legacy logging could break `CallsK`. Check that no legacy client lets
  `osTree`'s fractional split depend on the old body (only the three `unfold`s above do).
- **Strictness.** The step-time annotations of §1 still exist under `∃`. If Upamanyu wants them to be
  literal functions of `st` too, the call fractions and the files' `OsMeta` would have to move into
  client-held fragments. That is a much larger change, which this note does not size.
- **kaashoek's `putget-dist` finding** (`fsSemWithS`, `Premises.lean:36`, keeps the default
  `initLocal`). Fixing it is a *trusted* change and is kept separate from this untrusted one. Proposal:
  `initLocal st _ := FsInit st`, under `/fix-semantics` with sign-off. It is orthogonal to this design,
  which already assumes `FsInit` at `local_init`.

## 6. Collisions

- **kaashoek's WAL branches (#15).** `wal-nostorageok` (blocked on perennial#661) and `net-swap` do
  not touch `GooseLang/Ext/Fs` (kaashoek, 2026-11-23). The landed `wal-safe` work is the main user,
  through `AdequacyShared`/`TreeSharedKit`; stage 2 keeps its statements. A new WAL branch that
  unfolds `treeShared`/`treeCtx` should wait for stage 1 or use the wrappers.
- **dsverify ports on `Net/`** (#24 kits under `Dsverify/`; #28 `lib/remote`, etcd-dist,
  `net-swap`, `putget-dist`). Only stage 0/3's edit to `NetFsBridge.lean` (`CrashBootWp`'s `£ 1`) can
  conflict. Land it as one small commit and announce it on #28.
- **kvnet.** Stage 3 edits `TopBoot`, `ReplicaLinked`, `TopLevelRobustness`, and deletes `TopBridge`
  and `TopCrash`. Any kvnet relink in flight should land first, or rebase onto stage 3.
