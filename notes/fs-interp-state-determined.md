# One state-determined view of the file extension's tree (design, 2026-11-23, revised)

Upamanyu: "The ghost state inside of the state interp should just be determined from the state."
Revision: "Our goal is not to keep diffs in our git history minimal. Our goal is to end up with a
clean and complete proof. So, we should retire the legacy view if it's unnecessary." This is a
design only, against `lean` `f85bfe0827`, with perennial#683 part 1 landed as Perennial `48401b6ba`.
The first version, which kept two views, is superseded and in this file's history.

## 1. Today

The tree part of `osCtx` (`GooseLang/Ext/Fs/Ghost.lean:1409`) is a **mode**:
`treeCtx := (treeLegacy ∨ treeShared) ∗ commitRes` (`:1263`).
- Which disjunct holds is not a function of `st`.
- `legacyHolds` (`:1138`) holds every shared authority empty, whatever `st` is.
- `treeShared` (`:1252`) freezes the legacy history at `V0`. It also keeps the whole `γd` fragment
  itself, and the switch point `s0` as ghost state (`TreeCohS`, `:1225`).

These are updated off-step:
- `treeCtx_switchG` (`TreeSharedKit.lean:88`);
- `osShare_ctx`, `wp_osShareE` and `wp_osShareE_upd` (`TreeSharedSwitchE.lean:36,110,170`), and
  `wp_osShareE_acc` (`TreeSharedKit.lean:186`);
- `wp_osShare'` (`TreeSharedSwitch.lean:311`);
- `os_local_crash`'s shared branch (`CrashTok.lean:410`), with `crashMode`/`crashShared` (`:178,189`).

A crash can come before a generation's first step, so a crash frame that owns the shared invariants
needs the switch before the WP. That needs the interpretation, which is why `CrashAdequacyAcc.lean`,
`AdequacyShared.lean` and kvnet's `TopBridge.lean` (perennial#683 part 2) exist. Per-call and
per-file annotations (call fractions, `Γg`, `OsMeta`'s ghost fields) are not modes. They change only
in step proofs, and they stay (§5).

## 2. The single view

**Interpretation.** It keeps one shape, and the authority is a function of `st`:

```
treeCtx hL st := ∃ Γdf Γc Γg, ⌜FsTreeWf st ∧ TreeCohS st Γdf Γc Γg⌝ ∗
  gAuth γs (histMap (st.fs.roots, (st.fs.treeDur, st.fs.metaLog))) ∗
  gAuth γdfS Γdf ∗ gAuth γcS Γc ∗ callResS Γc ∗ gAuth γg Γg ∗ callResS Γg ∗ commitRes st
```

- `γd`, `γdf`, `γc`, `treeLegacy`, `legacyHolds`, `TreeCoh`, `rdRes` and `callRes` are deleted.
- `s0` goes, because every generation's log starts empty. So `TreeCohS` loses its legacy-prefix
  exemptions (`CallsK.after`'s `y < s0`, and `RootCoh`/`LogValid` from `s0`).
- `commitRes` sets `c` to `st`'s committed prefix.

**Start and crash hand out the shared view directly.** The shared view is the only view.
- `os_local_init` allocates `γn`, `γlen`, `γlog` and `γperm` already filled in (the claims of
  `claimsInit`, length 0, the empty log, every permission whole).
- `fs_start` allocates `osInv` and `osSharedInv`/`osAboveInv` together and returns
  `osShared R (treeDur, [])`. `fs_start` is a fancy update already, since it allocates `osInv`.
- At a crash, `os_local_crash` updates nothing. `crashRest` keeps the old `γs` authority and the
  closed-cut facts (`osCrash_relS`), plus the new generation's filled-in names.
- `crashRest_treeS'` (`TreeSharedCrash.lean:184`) allocates the new invariants and returns
  `osShared L' R V'`.
- `crashRest_region'` and `crashRest_treeWf'` keep their statements.
- `osTree`, `osDir`, `osDirFd`, `osCall`, every `wp_os*G`, `crashRest_tree`, `osTreeCrash_take`,
  `TreeCrashed` (as a client fact) and the switch lemmas are deleted.

**Adequacy.** There is one theorem per semantics. `fs_crash_adequacy`, `fsQ_` and `fsSQ_` take the
shape `fsSQ_crash_adequacyShared` has now (`AdequacyShared.lean:41`):
- `Hstart` and `Hwp` get `osShared`;
- the crash frame gets `osInv L'` and `crashRest`.

They are proved over Perennial's plain `goose_crash_adequacy`. `CrashAdequacyAcc.lean` is deleted.

**What legacy gave and the shared view must give.**
- *Exclusive ownership:* whole claims `osNames j (.except []) 1 h` on a region's directories, plus
  the key's whole `osCallPerm`. A directory rename needs the latter (`wp_osRenameDirS`,
  `TreeShared.lean:353`).
- *Exact directory reads:* the claim presented at each read (`wp_osDirReadNextS`).
- *A crash that leaves a prefix:* a new pure lemma, `regionCrashed_seq`. It applies to a region
  whose calls each began after the region's previous entry, as a single thread's do when it carries
  `osLogLb` from one call to the next. For such a region, `RegionCrashed`'s closed set is a prefix of
  the region's entries.

Every legacy spec has a shared twin: Unlink, Rmdir, Mkdir, OpenCreate, OpenFile, OpenDir, LstatDir,
CallBegin, DirReadNext, DirClose and Rename (file, dir, absent). DirSync is shared only. No client
needs exclusive direct ownership outside the invariant. The claims' authority sits in
`osSharedInv`, and whole claims and permissions are already the "exclusive tokens inside the shared
invariant".

## 3. Per-client migration (the clean end state)

No trusted change: `Impl.lean`, `Tree.lean`, `Paths.lean`, `Premises.lean` and Perennial's adequacy
stay as they are. No top-level statement changes, and these stay as they are:
- `TopLevelRobustness` specs;
- the osfs/netfs/bbolt `Results` statements (all execution-level);
- `etcd_wal_*`.

kvnet's top level gets stronger: it loses `Hb`.

| Client | Rewrite | Size (touched lines) |
|---|---|---|
| **`Ext/Fs` core** | delete `TreeSpecs{,DirFd,Meta,Open}.lean` (2.5k), `World.lean`'s legacy half (~500), the legacy parts of `TreeCommit`/`TreeCrashLb`/`TreeCrashCommit`/`CrashFiles`/`CrashTok` (~700), `TreeSharedKit`/`Switch`/`SwitchE` but their allocation helpers (~700), `CrashAdequacyAcc` (268), `AdequacyShared` (folded in); rewrite `treeCtx`, `os_local_init`/`crash`, `fs_start`, the three adequacy theorems, `crashRest_treeS'`; drop `s0` and the legacy-case splits from ~20 `TreeShared*.lean` step proofs; add `regionCrashed_seq` | −5.5k / +1.5k; 2-3 agent-weeks |
| **`Proof/os` legacy** | retire `Ns.lean`, `OpenFile.lean`, `Spec/os/OpenFile.lean` (shared `NsS`/`OpenFileS` exist); rebase the crash-aware file layer `Crash`, `CrashFile` (`cfInv`), `CrashFileQ`, `CrashOps`, `CrashSt` (`csInv`), `CrashStOps`, `CrashStSpec` (~4.2k) from "half of `osTree`" to "half of the name's claim plus a spine fraction", with `TreeOkI` restated over `RegionCrashed`. The by-fd operations and the pure parts (`cfRange`, `CrashOk`, which the real bbolt and the WAL's `Inv.lean` use) stay | ~1.5-2k of 4.2k; 1.5 agent-weeks |
| **walfs** (`SegLog*`, `DirSwap*`, `DS*`, `Boot`, Results 5.5k) | the heaviest client. Its 139 `osTree`, 20 `osCall` and 18 `TreeCrashed` uses move to whole claims on its directory (and, for `DirSwap`, on the swapped directories), `osCallPerm` whole for `rename` of a directory, `*S` specs, and `regionCrashed_seq` in place of `TreeCrashed`. The `DSTree`/`DSCheck` invariants restated over `NamesH` histories | ~3k of 5.5k; 2 agent-weeks |
| **crashlog** (`Boot` 702, Results) | `cfInv` users follow `Proof/os`; its start/crash (`startAt_start`, `treeCrashed_nil`) over the file's claim | ~300; 2-3 days |
| **bboltfs/minibolt** (Specs `Open`, `testMinibolt{,Concurrent}`; proofs `Open`, `CrashImg`, `CrashOk`, `DBCrash`, Results) | the three Spec files state `osSharedInv R ∗` the db file's claim, a spine and a call permission instead of `osTree 1 R V`; the crash proofs follow `csInv`'s new tree part; page/byte reasoning untouched | ~600-900; 1 agent-week |
| **WAL proofs** | already shared; `wal/BootCrash*` and `Crash` call `crashRest_treeS'`, which now returns `osShared` directly; a few `icases` | ~50-100 |
| **WalTester** | `fsSQ_crash_adequacyShared` renamed to the one `fsSQ_crash_adequacy` (same shape); `durable`'s copies unchanged | ~20 |
| **`etcdstart/WalAreas`, `runtime/StartFiles`** | drop `wp_osShareE`; take `osShared` from `fs_start` | ~60 |
| **osfs/netfs `Results`, `Net/Statement/NetFsBridge`** | `fsStartRes` holds `osShared`; `CrashBootWp`'s frame gains `£ 1`; the Results' proofs adapt to the new adequacy shape | ~150 |
| **kvnet** | `kvGen` holds `osShared`; `kvGen_boot` loses its `localCtx σ` argument and its switch; `kvRep_gen` proves `CrashBootWp` (plain adequacy plus `£ 1`); delete `TopBridge.lean`, `TopCrash.lean` (the pre-switch window no longer exists) and `Hb` in `TopLevelRobustness` | −400 / +80; 3 days |
| `GooseLang/Ext/OsFs/*` (`osFsExt`) | has no tree ghost; unaffected | 0 |

Total: about 7k lines touched, net about −6k. Roughly 8 agent-weeks, which can run in parallel after
stage 1.

## 4. Migration order

0. **Pin bump to a Perennial `lean` with `48401b6ba`** (#683 part 1, `£ 1` per crash). Adapt the
   callers (one extra `_`). `NetFsBridge` threads the credit to `CrashBootWp`.
1. **Shared-view adequacy and start, alongside legacy.** Land `fs_start'` (returns `osShared`),
   `crashRest_treeS'` returning `osShared`, the new `fs*_crash_adequacy` shapes, and
   `regionCrashed_seq`, beside the old ones. Allocating the shared names filled in at `os_local_init`
   needs `legacyHolds` gone, so this stage also makes the interpretation's shared half
   state-determined. The legacy half is not removed yet.
2. **Clients, in parallel, each landing alone** on the new API:
   - kvnet (needs stage 0);
   - WalTester, `etcdstart`, `StartFiles`, the WAL proofs;
   - `Proof/os`'s crash-aware layer, then crashlog and bboltfs;
   - walfs.

   Each deletes its uses of `osTree`/`wp_os*G`/`TreeCrashed`.
3. **Retire legacy.** Delete `treeLegacy`, `γd`/`γdf`/`γc`, the `wp_os*G` and `TreeSpecs*` specs,
   the switch lemmas and `CrashAdequacyAcc`. Drop `s0` from `TreeCohS` and re-prove the shared step
   proofs. Then the interpretation has exactly the shape of §2. This lands once `etc/importers.py
   --uses osTree` finds no user outside the files being deleted.

## 5. Risks and open questions

- **`regionCrashed_seq`.** It needs each call's start above the region's previous entry, carried
  through `osLogLb`. That is cheap for single-threaded walfs and crashlog. For minibolt's concurrent
  test, check that only one goroutine does path operations.
- **walfs's restatement** is the largest unknown. `DirSwap`'s invariants are stated over whole
  histories `V` (`DSTree`). Moving them to per-directory `NamesH` histories could reshape them, not
  just rename them. Do a spike on `DSTree` first.
- **The crash-aware file layer** (`csInv`): masks. Its invariant now nests `osShN` opens inside
  steps that already open `osN`. `osShN_sub` (`TreeSharedSwitch.lean:241`) handles this for the
  existing shared specs. Each `CrashStOps` spec needs `↑osShN ⊆ E`.
- **Credits:** `osSharedInv`'s body is timeless, so it needs no credit. The one `£ 1` per crash
  covers kvnet's `kdFileInvK`. A frame that must open non-timeless invariants under nested laters
  would need more; #683's argument allows any fixed number.
- **Strictness:** per-call fractions, `Γg` and the `OsMeta` ghost fields remain under `∃`, and are
  only ever updated at steps. Making them literal functions of `st` is not sized here.
- **Trusted, separate:** kaashoek's `putget-dist` finding (`fsSemWithS`, `Premises.lean:36`, needs
  `initLocal := FsInit`). It goes through `/fix-semantics` with sign-off, independently of this
  design.

## 6. Collisions

- **#15 (kaashoek).** `wal-nostorageok` and `net-swap` do not touch `GooseLang/Ext/Fs`. The landed
  `wal-safe` work is a client (stage 2). Any new WAL or bbolt branch should state its specs over
  `osShared` from now on.
- **#24/#28 (`Net/`, `lib/remote`, `putget-dist`, `net-swap`).** Stage 0's and stage 2's edits to
  `NetFsBridge.lean` (`£ 1`, `fsStartRes`) can conflict. Land them as small commits and announce them
  on #28.
- **kvnet.** Its stage-2 edits (`TopBoot`, `ReplicaLinked`, `TopLevelRobustness`; deleting
  `TopBridge`, `TopCrash`) should go after any kvnet relink in flight.
- **The real bbolt proof** (`Proof/go_etcd_io/bbolt`) is already shared. It imports only
  `CrashFile`'s pure parts, which stay.
