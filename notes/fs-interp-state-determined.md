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

## 7. Execution: the spike, and the interface fixed (2026-11-23)

Branch `fs-single-view/2026-11-23` (from this note's branch, `lean` `5dbc722ce9` merged).

### 7.1 The `DSTree` spike: the design holds

`walfs/DSClaims.lean` (checked, no `sorry`) restates `dirswap`'s `SafeH`/`MonoH` over two claims:
`(j, {wal, wal.tmp}, hw)` and, once `wal` can name a directory `J`, `(J, {seg}, hs)`. The facts
(`DInv`) quantify over every kept set `K` closed in the region (`RegionCut`, `RegionCrashed`'s first
clause) and read each name through `NamesH.valAfter … K`.
- `dinv_crash`: `RegionCrashed (regionOf …) n m' → SafeT j ko m'`.
- `dinv_init`: a fresh generation's claims (`NamesH.init`) on a `SafeT` tree start the facts.
- `dinv_log_other`: a step writing `wal.tmp` only (`mkdir`, `rmdir`) keeps them. The removes of the
  old `wal.tmp/seg` and the new `seg`'s create touch claims outside the invariant, so they no longer
  open it at all.
- `dinv_rename`: the rename onto the absent `wal` gives the facts with `J`'s claim tracked. This needs
  `hs.next ≤ e.start` (`osNames_next` before `CallBegin`) and `HistCoh hs` (`osNames_histCoh`).
- `dinv_rekey`: `ds_deposit`'s rekeying.

No reshaping was needed. The invariants got simpler, because the whole-history quantifier became a
two-claim one. walfs needs no prefix argument, since `Follows`-closure gives what the rename needs.
`regionCrashed_seq` stays in the interface for clients that reason about prefixes.

### 7.2 The interface (exact statements; proofs to follow)

**Interpretation** (`Ghost.lean`). It has no disjunction, no `V0` and no `s0`:

```lean
def treeCtx (hL : OsGS GF) (st : OsState) : IProp GF :=
  iprop(∃ (Γdf : GMap w64 (Ino × DirPhS)) (Γc Γg : GMap Nat CallV),
    ⌜FsTreeWf st ∧ TreeCohS st Γdf Γc Γg⌝ ∗
    gAuth hL hL.γs (histMap (st.fs.roots, ((st.fs.treeDur, st.fs.metaLog) : Hist))) ∗
    gAuth hL hL.γdfS Γdf ∗ gAuth hL hL.γcS Γc ∗ callResS hL st.fs.roots Γc ∗
    gAuth hL hL.γg Γg ∗ callResS hL st.fs.roots Γg ∗ commitRes hL st)
```

`TreeCohS st Γdf Γc Γg` loses its `s0` argument and the `s0le` field. `RootCoh`, `CallsK` and
`LogValid` lose their `s0` too, read at `s0 = 0`.

Deleted from `OsGS`: `γd`, `γdf`, `γc`. Deleted outright: `treeLegacy`, `treeShared`, `legacyHolds`,
`TreeCoh`, `rdRes`, `callRes`.

**Start resources.** `treeStart hL st := osSwitchKitG hL st.fs.roots (st.fs.treeDur, [])`. These are
the shared names, filled in: the whole `γs` element, the `γn` authority at `claimsInit`, length 0,
the empty log, every permission whole, and the whole claims. `os_local_init` keeps its statement
(`|==> ∃ hL, osCtx hL st ∗ osStart hL st`).

**`osShared`** moves to `TreeSharedRes.lean`, with the same body:
`osSharedInv R ∗ osAboveInv ∗ osCallPerms R ∗ osLogLb V.2.length ∗ [∗list] j ∈ dirsOf V, osNames j
(.except []) 1 (namesOf V j (.except []))`.

**`fs_start`** (`Adequacy.lean`):

```lean
theorem fs_start [hG : HeapGS .hasLC GF] (σ : state) (h : FsInit (extLocal fsExt σ.world)) :
    ⊢ extsLocalStart (GF := GF) σ.world ={⊤}=∗
      osInv (L := hG.goose_localGS) ∗
      ([∗map] i ↦ f ∈ (extLocal fsExt σ.world).fs.files, osFileStart (L := hG.goose_localGS) i f) ∗
      osShared (L := hG.goose_localGS) (extLocal fsExt σ.world).fs.roots
        ((extLocal fsExt σ.world).fs.treeDur, [])
```

`fs_startS` (`AdequacyS.lean`) is the same, for the `S` semantics.

**`crashRest`** (`CrashTok.lean`) loses `V`, `γd`'s authority, `crashMode`/`crashCommit` and
`TreeCrashed V V'`:
- it keeps `gAuth hL γs (histMap (crashed state))` and `crashShared`'s pure facts (`TreeWf`, `Starts`,
  the closed cut `S` with the committed entries, `V'.now`'s slots as `slotAfter … S`) and `commitRes
  hL st`;
- `treeLeft hL' R V' false := treeStart hL' st'`, with `V' = (st'.fs.treeDur, [])`;
- `crashRest Q hL hL' D tt V'` keeps its parameters.

`crashRest_region'` and `crashRest_treeWf'` keep their statements.

```lean
theorem crashRest_treeS' (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (V' : Hist) (R : Roots) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D false V' ={E}=∗
      ⌜V'.2 = []⌝ ∗ osShared (L := L') R V' ∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D true V'
```

**`regionCrashed_seq`** (`CrashRegion.lean`, pure):

```lean
def RegionSeq (cl : List Claim) : Prop :=
  ∀ c ∈ cl, ∀ c' ∈ cl, ∀ x e E y e' E', (x, e, E) ∈ c.2.2.ents → (y, e', E') ∈ c'.2.2.ents →
    y < x → y < e.start

theorem regionCrashed_seq {cl : List Claim} {n : Nat} {m' : Tree} (hs : RegionSeq cl)
    (h : RegionCrashed cl n m') :
    ∃ t, (∀ c ∈ cl, ∀ y e E, (y, e, E) ∈ c.2.2.ents → y < n → y < t) ∧
      ∀ c ∈ cl, ∀ b, c.2.1.Mem b → m'.entry c.1 b = c.2.2.valAfter c.1 (· < t) b
```

**Adequacy.** There are three theorems, `fs_crash_adequacy`, `fsQ_crash_adequacy` and
`fsSQ_crash_adequacy` (semantics `True`, `Q`, `SQ`/`Q`). Each has one shape, proved directly over
Perennial's `goose_crash_adequacy`. `P : GooseLocalGS GF → IProp GF` has no history index.
- `Hstart` gets `osInv`, the files, `osShared R (treeDur, [])` and `ownGoState`, and gives `P L`.
- `Hwp` is `P L -∗ threadTok ={⊤}=∗ WP … ∗ frame`.
- The frame gets `crashed`, `osInv L'`, `crashRest Q … [] false V'`, `ownGoState ∅` and `£ 1`, and
  gives `P L'`.

The frame makes the next generation's `osShared` itself, with `crashRest_treeS'` and the old
generation's `osSharedInv` (persistent, kept in its context). This differs from §2's wording ("`Hwp`
gets `osShared`"). Only this shape needs no access to the interpretation, so it is the one that
runs over plain `goose_crash_adequacy`. `fsSQ_crash_adequacyShared`, `AdequacyShared.lean` and
`CrashAdequacyAcc.lean` are deleted.

**Shared specs.** `TreeShared.lean`'s statements stay verbatim: `wp_osCallBeginS`,
`wp_osCallBeginAboveS`, `wp_osCallBeginGuardS`, `wp_osLstatDirGuardS`, `wp_osUnlinkS(_none)`,
`wp_osRenameFileS(1)`, `wp_osRenameDirS`, `wp_osRenameAbsentS`, `wp_osMkdirS(G)`,
`wp_osRmdirS(G)(_none)`, `wp_osLstatDirS`, `wp_osOpenCreateS`, `wp_osOpenFileS`, `wp_osOpenDirS`,
`wp_osOpenDirChildS` and the rest of the file. The same goes for the claim and spine laws
(`osNames_split/merge/rekey/next/frac/agree`, `osNames_histCoh`, `osClaims_log`, `osPathS_*`,
`osCallPerm_*`) and the `TreeShared{Read,DirFd,Create,Out,Guard,Trunc,…}` specs.
`wp_osShare`/`wp_osShareE*` are deleted.

**Deleted client API.** `osTree`, `osDir`, `osDirFd`, `osCall`, `tree_*` (`tree_combine`,
`tree_halves`, `tree_agree`), every `wp_os*G`, `wp_metaStep`, `TreeSpecs{,DirFd,Meta,Open}.lean`,
`crashRest_tree`, `osTreeCrash_take`, `TreeCrashed` as a client fact, `treeCrashed_*`,
`CrashAdequacyAcc.lean` and `AdequacyShared.lean`.

### 7.3 Work split (helpers on disjoint files, merged here)

1. **Scaffold.** The statements of §7.2 land in the core, proofs `sorry`, on `fs-sv-scaffold`. That
   branch is never landed, but it can be checked against, so the clients start before the core is
   proved.
2. **Core proofs:** `Ghost`, `World`, `CrashTok`, `CrashFiles`, `TreeShared*`, `Adequacy*` and
   `CrashRegion`, plus the deletions.
3. **Clients**, each in its own files against the scaffold: `Proof/os` (crash-aware layer); walfs
   (`DSClaims` grows into `DirSwap`; `Boot`/`SegLog` the same way); crashlog; bboltfs/minibolt; the
   WAL, WalTester, `etcdstart` and `StartFiles`; osfs/netfs `Results` and `NetFsBridge`; kvnet, last.

Stages land once the core has no `sorry`. With the legacy API deleted, there is no "alongside"
stage. Stages 1-3 of §4 land as one core stage, together with every client that imports a deleted
name. kvnet's relink follows.
