# Plan: the WAL tester and the server onto the fsExt WAL specs; retiring `absDiskExt` (W4c over fsExt)

**Date:** 2026-11-14. **Status:** plan, no work started. Survey of `wal-int` `074c7d97cc`. Context:
`notes/wal-fsext-plan.md` (the 12 WAL specs over `fsExt`; §3 "Clients", §8 "Inventory" and "Links"),
`notes/decisions.md` "One file semantics, `fsExt`; power loss only", and the paused absDisk W4c
(`notes/wal-w4c-handoff.md`). Abbreviations: `S/` = `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/`,
`Sp/` = `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/`, `T/` =
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/wal/`, `AD/` = `GooseLang/Ext/AbsDisk/`.

## 0. Headline

- The tester (`examples/etcd/wal`, the closed theorems `etcd_wal_adequate`/`etcd_wal_safe`, **never
  stated**: W4c was paused at step 3 of its plan) lives in the **main tree** and is written over
  `[HasExt absDiskExt] [HasExt durableExt]`. The new specs live in the `LinuxFs/` part, which nothing outside
  imports. So the tester moves **into the part** (§2, U1); there is no in-place rewiring.
- The server (C6) does **not** use the WAL specs yet: no server proof calls `wal.Open/Create/Save/...`
  (`grep` of `Proof/go_etcd_io/etcd/server/v3/etcdserver/`: only the package-init instance,
  `BaseApply.lean:79-86`, and `Init.lean:68,291`; its WAL is the names-only translation, modelled by
  `storage.walOf`/`walBaseLb`, `ApplyAllSnap.lean:526`). C6 is **unwritten**, and it can only be written over the
  part's specs once the part's `os` becomes the main tree's (the bbolt port, `notes/bbolt-port-plan.md`): C6 is
  gated on that, not on this track (§4).
- The tester's oracle file goes through `examples/lib/durable` (`oracle.go:171-184`), i.e. `durableExt`. Moving
  the tester onto `fsExt` therefore needs `lib/durable` translated **with bodies** in the part and proved over
  `fsExt` (U2): the Go is already written over `os` (`durable.go:33-88`), only the main tree's trusted model
  (`TrustedCode/.../lib/durable.lean`) is extension-backed.
- What the WAL track can retire: `absDiskExt`'s **steps and world-assumption list** (`AD/Impl.lean`'s
  `AbsDiskStep`, :253, and `ExternalOp absDiskExt.name ...`), the 11 main-tree WAL axioms and `fileutil.TouchDirAll`'s,
  `WalBodies.lean`, `WalDisk.lean`'s `durableResvD` (:184), the tester's `purgeRound` axiom. **Not**: the pure
  types `AbsDiskState`/`WalDur` (`AD/Impl.lean:163,181`), which the new proofs are stated in (`walInv_alloc`'s
  `s`, `WalsBounded`, `S/Inv.lean:661`) and must move to a pure module; `durableExt` (kvdurable's 20+ files and
  `etcdstart/DurableExt.lean` use it); `osFsExt` (real bbolt's).

## 1. What depends on the old axioms now (file:line)

The main-tree axioms: `Proof/go_etcd_io/etcd/server/v3/storage/wal/{Create,Open,Exist,Repair,
ValidSnapshotEntries,WAL__Close,WAL__ReadAll,WAL__ReleaseLockTo,WAL__Save,WAL__SaveSnapshot,WAL__Sync}.lean:26`
(`axiom wal.*.wp_proof`), `Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/TouchDirAll.lean:19`, the tester's
`T/purgeRound.lean:25` (purgeRound, approved 2026-11-12), and the generated init axioms
(`.../storage/wal/Init.lean:42,65`; fileutil's, walpb's: these stay, regenerated for the part).

Their users, outside their own files:
- **The tester** (`T/`, 33 files). Directly over absDisk/durable:
  - `T/Defs.lean:338` `tOracleFile` (over `DurableState`), `:346` the binders, `:378-384` `TInvBody`
    (`durableOwnM`, `walArea`, `dirDurable`, the `if o.created ∨ od.isSome then dirDurable` clause);
  - `T/Crash.lean:18,71-178` `tester_crash`: `durableOwnM_crash_keep`, `absDiskCrashStart_split` (:92),
    `walArea_crash_keep` (:101), `dirDurable_crash_keep` (:102,117,150), `walDiskAt_crash_keep` (:118),
    `walDiskAt_crash_any_keep0` (:151), `durableOwnM_reserved` (:77,178);
  - `T/PurgeBody.lean:49-141` (`absCutLePur` over `AbsDiskStep`, the `"WalPurge"` ExternalOp at :141) and
    `T/purgeRound.lean:16`, `Spec/.../examples/etcd/wal/purgeRound.lean:6,30`;
  - the other 28 (`Rep`, `RefLemmas`, the ref.go/oracle.go function proofs) are pure Go over `WalHist`: no
    extension, they move unchanged (binders only).
- **`Proof/go_etcd_io/etcd/server/v3/storage/{WalDisk,WalViews,WalBodies}.lean`** (`[HasExt absDiskExt]`:
  `WalDisk.lean:174,184`, `WalViews.lean:24,105`, `WalBodies.lean:63`), the main-tree vocabulary the axioms
  are stated in; `WalHist.lean` (pure; stays).
- **`LinuxFs/GooseLang/Ext/AbsDisk/{Impl,Specs}.lean`**: generated copies (`etc/gen-part-copies.py:72-73`) the
  part's WAL proofs import for `AbsDiskState`/`WalDur`/`walImg`.
- **The server**: nothing beyond the init instance (above). `etc/api/absdisk.txt` and
  `interface/GooseLang/Ext/AbsDisk/*.txt` list the API.

## 2. The tester onto the new specs: statement differences

Each old axiom maps to the part's spec of the same name (`Sp/<F>.lean`), linked in `S/Link.lean`
(`etc/gen-link.py --walfs`, 195 results). What a tester call site must now supply:

| call | new premises / resources (Sp/) | source in the tester |
|---|---|---|
| `Create` | `InArea r dir nm`, `NameOk nm` (no NUL), `dir.length < 2^59`, `cleanAbsPath r`, `mp ≠ nil`, `md.length < 2^41`, **`md ≠ []`**, `WalMarshalCreateOk Mr` (Create.lean:84-85); `walAreaRes jr`, `osCallPerm 1`, `walUnlockedTok` (:88); error arms: token+perm back, or `Q ∗ osCallPerm ½` (:96-98, Q4(b)) | names are the tester's constants (`tWalDir root`); `md` the tester's fixed non-empty metadata (check `wal.go`: if it passes `nil`, a tester change, T-11); `dir` length from the `root` argument: a premise of the closed theorem |
| `Open`, `Repair`, `ValidSnapshotEntries`, `Exist` | the same name premises (Open.lean:46, Repair.lean:51, VSE.lean:50, Exist.lean:51), `osCallPerm 1 ∗ walUnlockedTok`; `Open` success keeps `osCallPerm ½` with the pipeline (`walOpeningF`); `Repair` returns `(walUnlockedTok ∨ b = false)` (Repair.lean:59) | as Create; the tester stops on `Repair = false` (check) |
| `Save`, `SaveSnapshot` | per-entry encoding `< 2^40` bytes, indices `< 2^64-1` (`walInvBody_append`'s `hox`); honest error post `∃ d, Q d` (token, handle lost) | the tester's entries are `entData` of bounded size (`rnd`): a pure bound lemma |
| `ReadAll` | `walAreaOk` (persistent), `osCallPerm qc`; model premises `U.Ok Mr`, `U.SnapCoh`, `WalHsOwn P U HsO` | discharged by the instantiation of `P`/`U`/`Mr` (U4) |
| `Close`, `ReleaseLockTo`, `Sync` | `walUnlockedTok ∗ osCallPerm 1` back on success (Close.lean:50); `unl` raises are bookkeeping (no lock model, §6 Q1 of the main plan) | — |
| `purgeRound` | **no fsExt statement possible** without a lock model (main plan gap 3, Q1 deferred [user]) | see U6 |

The lock token flow differs from the absDisk specs: the tester must thread `walUnlockedTok ∗ osCallPerm 1`
through every incarnation (one token, minted at boot, U3) and `osCallPerm ½` while a WAL is open.

**Model premises at instantiation (U4)**: the Link's results are generic in `P : WalPbIn GF`, `Mr`, `C`, `U`,
`HsO` and take the laws `h_WalPbIn_{GetIndex,IsEmpty,MarshalEnt,MarshalHs,Nil,UnmarshalEnt,Zero}Law` (plus
`MustSync`, `GetTerm`, `CloneHs`), `U.Ok`, `U.SnapCoh`, `WalHsOwn`, `WalDecEnvSupply`. The tester picks raftpb's
real model (raft's `pbMsg` specs, `Spec/google_golang_org/protobuf/proto/`) and proves each law once, in a module
`S/RaftModel.lean` that C6 will reuse. `WalDecEnvSupply` is true of Go but unprovable for `errors.newVar`'s lost
allocation identity (Perennial gap): stays a hypothesis until the Perennial change lands.

## 3. Boot: what the adequacy theorem must establish

From `fsExt`'s initial state (`FsInit`, the area absent or a WAL directory present) the boot of each generation
must produce `walAreaOk`, `walAreaRes jr`, `walUnlockedTok`, `osCallPerm 1`, via `walInv_alloc`
(`S/Crash.lean:495`). Its premises, each a boot obligation:
- `walStart ... s V.now` (the WALs found at boot as the abstract state `s`) and `hV : V.2 = []`;
- `hcl` (claims match the boot names), `harea : WalsCreateOk jr cl`;
- `hdirs`/**`hdirs1`**: every WAL directory `nm` under `jr` is claimed wholly (`NameSet.except walTmps`) exactly
  once, and no other claim on that inode overlaps it: the tester's area must contain **no other file of the
  WAL directories** than the WAL's (segments, `.tmp`s) — the oracle file and the purge's state live outside
  `tWalDir root` (check `wal.go`'s paths; else a premise);
- `hdok : DirsOk R s cl 0`, `hav : DirsAvoid R jr s` (directory durability after any crash, through no WAL slot);
- `hJm` (the temporary directories' inodes), `hnames`/`hnok` (`NameOk` of every name claim);
- **`hbd : WalsBounded s`**: every WAL found has metadata `< 2^41`, **non-empty**, and no maximal index
  (`S/Inv.lean:661`): an invariant the tester keeps across generations (its `md` is fixed and non-empty;
  indices from the oracle's bound `tHistWf`);
- `walTmpsRes` of each directory's `.tmp`s; the `.touch` probe ownership for `walAreaRes`'s `tmpClTouch`
  (`S/CreateDefs.lean:122-129`): a leftover `.touch` comes from the crash's `osFileStart` (`osFileStart_trFile`);
- `walAreaOk`'s pure parts (`S/CreateDefs.lean:95`): **`ReceiptBoundLe GF (2^62)`** (the step receipts'
  bound: fixed by the adequacy theorem's constants, `notes/bounds-plan.md`) and `Mr.encState hs < 2^32` (raft's
  `HardState` is three varints: U4).
- The crash step: the old generation's `walInv` closed with its contents (`walInv_crash`), the new one
  re-allocated by `walInv_alloc`; this replaces `tester_crash`'s `walDiskAt_crash*_keep` family.

## 4. Work units, hardest first (estimates in agent sessions)

- **U0 (0.5) Decisions** (§6) recorded; the tester's Go audited for §2's premises (`md`, `NameOk`, path
  lengths, the oracle's path outside the WAL directory, `Repair = false` handling).
- **U3 (3-4) Boot and crash: `walInv_alloc` from `FsInit` and from a crash image.** The hardest: build `walStart`
  from an arbitrary on-disk WAL (`WalAbs` of the bytes and names, main plan §3 "C6 gate 2"), the claim list
  satisfying `hdirs1`/`hdok`/`hav`, `WalsBounded` from the previous generation's invariant, the `.touch`
  files. A lemma `walBoot : FsInit/crash state → ⊢ |==> walAreaOk ∗ walAreaRes ∗ walUnlockedTok ∗ osCallPerm 1`
  in `S/Boot.lean`, reused by C6.
- **U2 (2-3) `lib/durable` over fsExt in the part**: translate `examples/lib/durable` with bodies into `LinuxFs/`
  (project `durable`'s part, as the WAL's); missing part specs `os.CreateTemp`, `os.ReadFile`,
  `File.WriteString`, `os.Open` (dir), `errors.Is(fs.ErrNotExist)`; prove `Read`/`Write` (retry loops) over a
  crash-tracked claim disjoint from the WAL area; a `durableOwn`-like predicate and its crash lemma. Shared with
  the later `durableExt` retirement (kvdurable).
- **U4 (2) The raftpb model and its laws**: instantiate `P`, `U`, `Mr`, `C`, `HsO`; prove the
  `WalPbIn.*Law`s, `U.Ok`, `U.SnapCoh`, `WalHsOwn`, `Mr.encState < 2^32`, `WalMarshalCreateOk`. Reused by C6.
- **U1 (1) Move the tester into the part**: retarget goose project `etcd-wal` to the `LinuxFs` root (its
  `lean_roots` already map `os=`/`io/fs=`); `git mv T/` and its specs to `LinuxFs/Proof/...`; `gen-init.py`'s
  `LFS_PKGS`; the 28 pure files rebuilt with new binders.
- **U5 (2-3) Restate and re-prove `TInvBody` and `tester_crash`** over `walAreaOk`/`walSyncedLb`/`walNamed`/
  `walDirIs` and U2's predicate (main plan §3 "Clients"); then the rest of the paused W4c step 3 (oracle.go,
  wal.go: ~25 functions, the handoff's list) over the new specs, with the token flows of §2.
- **U6 (1, or blocked) `purgeRound`**: drop it from the tester (a Go change to our own example: the tester's
  purge exercises the lock model only) **or** wait for the lock model [user]. Recommended: drop now, restore with
  gap 3.
- **U7 (2) Close the Link's hypotheses** the tester's results reach (§5), then state `etcd_wal_adequate`/
  `etcd_wal_safe` over `fsExt` (`FsInit`, area absent; premises: `root` clean and short, W1's no-collision) —
  **hard stop before stating** (exported statement).
- **U8 (1) Retire**: delete the main-tree WAL axioms and specs (`Proof/`/`Spec/.../storage/wal/*.lean` but `Init`),
  `TouchDirAll`'s axiom, `WalBodies.lean`, `WalDisk.lean`'s absDisk parts, `AD/Impl.lean`'s steps and
  `absDiskExt` (keeping `AbsDiskState`/`WalDur`/`walImg` in a pure `Proof/go_etcd_io/etcd/server/v3/storage/WalAbs.lean`,
  the part's copy regenerated), `etc/api/absdisk.txt`, the interfaces; `tcb-baseline` `--check --update`.
  The server's names-only WAL stays until C6.
- **C6 (later, gated on the bbolt port's promotion of the part's `os`)**: the server's `bootstrapWALFromSnapshot`/
  `openWALFromSnapshot` over U3's `walBoot` and U4's model; the restart interface I1-I11
  (`notes/wal-crash-handoff/restart-wal-interface.md`); gate 8 (the server's purge) needs the lock model.

Total before C6: about 15-18 sessions. Order: U0, U3 ∥ U2 ∥ U4 (independent, separate worktrees), U1, U5, U6,
U7, U8.

## 5. Unproved hypotheses blocking a closed result

From `S/Link.lean` and `etc/tcb-collections/wal-fsext.txt`:
- `sorry`s: `wal.Create.wp_proof` (cleanup arms, `S/Create.lean:145,157,191`: blocked by design, unregistration
  proposed), `WAL.ReadAll.wp_proof` (EOF stop), and `S/Repair.lean:411`, `S/RepairLoop.lean:65`;
- Perennial gaps (true of Go): `errors.{AsLinkError,IsErrno,IsPathErrnoEof,IsPathErrnoNotExist}`,
  `fmt.ErrorfErrsNot`, `filepathlite.IsAbs` (`stringslite.HasPrefix` has no body), `WalDecEnvSupply`;
- trust-boundary extension: `proto.UnmarshalWalRecordE` [user];
- the WAL's own: `WAL.renameWALUnlock.spec` (false as stated, ledger), `wal.validSnapshotEntries{Absent,Pinned}`,
  `fileutil.CheckDirPermission` (proved on `wal-leaf5-modeperm`, unmerged);
- model laws: U4.

## 6. User-review items gating landing on `lean`

1. The tester's closed theorems' statements (`etcd_wal_adequate`, `etcd_wal_safe` over `fsExt`) — hard stop.
2. Dropping `purgeRound` from the tester (or the lock model, main plan Q1) and retiring its approved axiom.
3. The provisional trusted items the tester's results would make reachable: W1's no-collision premise (Q2), the
   drafted `syscall`/`os` models (§6 "Missing trusted models"), `io.ReadFull`'s restated axiom, `Readdirnames`'
   `growslice` assumption, `proto.UnmarshalWalRecordE`, the fork's `O_TRUNC` fix (push pending).
4. The tcb-baseline changes: −12 WAL axioms, −1 purgeRound, +the part's copies (15 generated axioms) and any of 3.
5. `lib/durable` with bodies in the part (a new translated project and its `os` specs).

## W4c U3 log

**First session (branch `wal-u3`, 2026-11-14): the first boot proved; the crash boot designed, not
proved.** No `sorry`, no axiom, nothing trusted changed; no statement of an existing lemma changed.
Modules (`S/`): `BootPure` (pure), `BootStart0` (the first generation's `walStart`), `Boot0` (`walBoot0`).

- **`walBoot0`** (`S/Boot0.lean`): at the shared mode's switch (`wp_osShare`'s `osSharedInv R` and the whole
  claims `[∗list] j ∈ dom V.now, osNames j (.except []) 1 (namesOf V j _)`), with `osInv`: `∃ W, walAreaOk C Mr R
  jr r ∗ walAreaRes jr ∗ walUnlockedTok ∗ walCrashTok ∗ walPast (walBoot0St r)`, and back the area's claim on
  its names holding an entry (`(.except []).inter (areaOthers V.now jr)`) and every other directory's claim.
  `osCallPerm 1` is untouched (the program keeps `wp_osShare`'s). It allocates the ghost state
  (`walStart_boot0`: `walGhost_init` over `walBoot0St r = ⟨r, ∅, {r}⟩`, the steps' bound from `⧖ 0`), splits the
  area's claim (`osNames_split` along `areaOthers`), and calls `walInv_alloc` with `cl` = the one area claim
  `(jr, .except (areaOthers V.now jr), _)`, `Jm = ∅`, `qs = 1` (`osPathS_root`).
- **Its premises** (each a world premise of the closed theorem's first boot; the user reviews them):
  1. `hV : V.2 = []`: `wp_osShare` at the program's first step (not a world premise).
  2. `hR : RootsOk R`: `FsInit`.
  3. **`hr : (r, jr) ∈ R`, the area a root.** `Create` needs `dirDurable r` (`r ∈ s.dirs`), and no `fsExt` step
     adds a durable directory (`TouchDirAll`'s spec gives a commit bound, not `dirDurable`): the boot state must
     hold it, and `walInv_alloc`'s `DirsOk R s cl 0` must then hold for every tree the claims `cl` allow. A
     directory below a root resolves in such trees only if `cl` holds its spine's claims, which `walInv_alloc`
     also takes as the program's `osPathS R r` (the same `.only [c]` keys): so a durable directory must be a
     root (`DirsRoots`, `BootPure.dirsOk_roots`/`dirsAvoid_roots`). For the tester: `tWalDir root = root/<nm>`,
     the area its root.
  4. `hjr : jr ∈ V.now`: from `FsInit`'s `TreeWf` (`Reach.root`); left a premise (U7 discharges it).
  5. **`hslots : ∀ b, AreaSlot b → V.now.entry jr b = none`**: the area has no entry at any name a WAL
     function may change (a WAL name — non-empty, no `/` or `.` — or `nm.<sfx>`: every name not starting with
     `.`). Hence **no WAL at the first boot** (as `absDiskInitOk`'s `s.wal = ∅`, etcd-grove-81): a WAL found on
     disk would need `WalsStart` (its bytes decoding to some `WalDur` with a layout) and `WalsBounded` (no index
     `2^64-1`, metadata non-empty and `< 2^41`), facts of the decoded records that an arbitrary disk need not
     meet (an older etcd's names, a maximal index): the C6 gate's "written by etcd at the pin". And the
     program's part of the area holds no entry, so `walAreaRes`'s `SubCover`, `TmpOk` and `.touch` files are
     vacuous. **Tester check (U0):** the oracle file and every other file of the tester must be outside the
     area or named with a leading `.`.
  6. `hrb : ReceiptBoundLe GF (2^62)`: the adequacy theorem's constant (`notes/bounds-plan.md`, rule 1).
  7. `henc : ∀ hs, (Mr.encState hs).length < 2^32`: U4's law.
  `WalsBounded`, `DirsOk`, `DirsAvoid`, `hdirs`/`hdirs1`/`hnames`/`hnok`/`hJm`, `walTmpsRes`, `walOthersL` are
  all discharged (no WAL directory, one claim).
- **`BootPure`**: `DirsRoots R s` (every durable directory a root) gives `DirsOk R s cl n` for any `cl, n` and
  `DirsAvoid R jr s`; `walsBounded_crash : walStCrash s s' → WalsBounded s → WalsBounded s'` (a crash keeps the
  metadata; an image's indices are the old history's); `dirsRoots_crash`.
- **The crash boot (next unit, not started).** From `walInv_crash`'s outputs (`walStart L' W' … s' V'.now`,
  `walPast`, the tokens, `DirsAvoid R jr s'`) and the new generation's `wp_osShare` claims on `V'.now`. What it
  needs that the first boot did not, and what is missing:
  (a) **`walInv_crash` must export `⌜WalsBounded s'⌝`** (its body's `Hbd` through `walsBounded_crash`: one line)
  **and `⌜DirsRoots R s'⌝`** (needs the invariant to keep `DirsRoots R s`: no step changes `s.dirs`, so a framed
  conjunct, or `DirsRoots` in place of `DirsOk`+`DirsAvoid`, which it implies). Statement changes to
  `Crash.lean`/`Inv.lean` (129 importers, 37k lines rebuilt): deferred to that unit, not made here.
  (b) the claims: per present WAL `nm` (directory `J`, `lay.j`), `(J, .except walTmps)` in `cl`, `(J, .only
  walTmps)` split off to `walTmpsRes J`, `(jr, .only [nm])` in `cl` (`hnames`), the area claim `.except (Wn ++
  others)`; `hdirs1` from `TreeWf`'s unique naming (distinct WAL names, distinct `J`; the crash's `FsInit` gives
  `TreeWf` of `V'.now`).
  (c) whole files (`trFile`, from `osFileStart` via `osFileStart_trFile`) of every WAL directory's non-`.wal`
  entries (`walOthersL`, `walTmpsRes`) and of each `nm.tmp/.touch` (`tmpClTouch`): `crashRest` keeps them
  untaken (`walInv_crash` takes the segments only); a take of named non-segment files is needed.
  (d) **not derivable from the WAL invariant, premises of the crash boot** (the client's crash invariant, U5,
  must carry them, or the WAL invariant must gain them): every WAL directory and every `nm.<sfx>` directory of
  the area holds only files (`tmpEnt (dir _) = False`, `TmpOk`, `SubCover`); the WAL creates nothing else there,
  but no invariant records that the claims' histories hold only files.

**Second session (branch `wal-u3b`, 2026-11-14): (a) and (c) done; (d) not derivable as decided; (b) designed.**
No axiom, nothing trusted changed. **For concurrent branches (merge note):** `walInvBody`'s last conjunct is now
`⌜WalsBounded s ∧ DirsRoots R s⌝` (`DirsRoots` moved from `BootPure` to `Inv.lean`, with `DirsRoots.congr`/`.upd`):
a step's `%Hbd` is the pair; rebuild with `⟨walsBounded_… Hbd.1 …, Hbd.2⟩` (`Hbd.2` is accepted as is when the
new state is `{s with wal := …}`; `Hbd.2.upd` for `absDiskUpd`); a step keeping `s` closes with `Hbd` unchanged.
`walInv_alloc` takes `(hdr : DirsRoots R s)` after `hbd`. `walStart`'s pure part gained `∀ i ∈ is, Named m i →
(fo i).isSome` (second conjunct). `entsOf_lookup` moved from `Crash.lean` to `BootCrashPure.lean`.
- **(a)** `walInv_crash` returns `WalsBounded s' ∧ DirsRoots R s'` (`walsBounded_crash`, `dirsRoots_crash`).
- **(c)** `walInv_crash` also returns `[∗list] i ∈ bootFiles V'.now jr, trFile i False` (new generation): every
  file of the crashed tree at a non-`.wal` name of a directory at a WAL name of the area (the others and the
  pipeline names `0.tmp`/`1.tmp`), and at `.touch` of a directory at `nm.tmp` (`BootCrashPure.lean`). Distinct by
  unique naming, a new premise **`hu : UniqNames V'.now`** (`TreeWf`'s last part of the crashed tree: `MachineCrash`
  does not state the crashed tree well formed; a lemma "replaying a `Closed` set of logged operations on a
  well-formed durable tree keeps `TreeWf`" would discharge it, not proved). An old segment's inode found at a
  non-`.wal` name (a `cut` rename the crash dropped) comes from its segment start (`walStart` keeps only the old
  segments not in `bootFiles`; the new layouts' segments are at `.wal` names, so none is lost); the rest from
  `crashRest` (`crashRest_take_named`, `CrashTakeNamed.lean`: no old resources needed).
- **(d) "WAL directories and `nm.<sfx>` directories hold only files" cannot be a fact of the WAL invariant as
  it stands.** A fact about the crashed tree comes from the claims the invariant holds (`RegionCrashed cl n`). The
  entries in question are under claims the invariant does not hold when the crash comes: the pipeline names'
  `tmpClaim`s while a write handle holds them (`filePipeline.alloc` creates `0.tmp` with the whole claim, no
  invariant step), the names `Repair` lends (`lendKey`), the whole claims of every directory under an `nm.<sfx>`
  (`walAreaRes`'s `areaCls`, the program's), and `Create`'s `nm.tmp` directory's claim. Only the WAL directory's
  own claim `(J, .except walTmps)` is the invariant's. Making it derivable means the invariant keeping a share of
  those claims (the pipeline's and `Create`'s file creations becoming invariant steps through `osAU`, and
  `walAreaRes`'s subtree claims shared): a change to `walAreaRes` (client-visible vocabulary) and to the
  pipeline's ownership — **left to the coordinator/user** (not done). Until then it is the crash boot's premise
  **`hfo : ∀ b J, AreaSlot b → V'.now.entry jr b = some (.dir J) → FilesOnly (entsOf V'.now J)`** (true of the Go
  code: nothing creates a directory there; not dischargeable by a client either).
- **(b), next: `walBootCrash`** (new generation, at its `wp_osShare` with `V = V'`, `V'.2 = []` from
  `crashRest_treeS`), designed: `cl` = the area claim `(jr, .except (Wn ++ others), _)` (`Wn` the present WALs'
  names, `others` the area's names holding an entry that are no `AreaSlot`, given back as at the first boot), per
  present WAL `nm` at `J`: `(J, .except walTmps, _)` and `(jr, .only [nm], _)`; `(J, .only walTmps)` → `walTmpsRes J`
  (files from `bootFiles`, `hfo`), `Jm` = the present WALs' directories; `hdirs1`/`hJm`/`hnames`/`hnok` from
  `UniqNames` and `TreeWf` (`NameOk`); `hdok`/`hav` from `DirsRoots` (`BootPure`); `walOthersL` from `bootFiles`;
  `walAreaRes`: `areaCls` = each `nm.<sfx>` directory's whole claim tagged by its name, `SubCover`/`TmpOk` from
  `hfo`, `tmpClTouch` from the `.touch` files of `bootFiles`. Premises: `hu` (or `TreeWf R V'.now`), `hfo`.

## W4c U2 log

**First session (branch `wal-u2`, 2026-11-14): `lib/durable` translated into the part, its vocabulary
and the `Read`/`Write` specs stated over `fsExt`; nothing proved yet.** No axiom, no trusted model,
no `sorry` (no proof file yet). Modules: `LinuxFs/{Code,GeneratedProof}/github_com/mit_pdos/etcd_grove/
examples/lib/durable.lean` (generated), `LinuxFs/Proof/.../examples/lib/durable/{Defs,PkgInit}.lean`,
`LinuxFs/Spec/.../examples/lib/durable/{Read,Write}.lean`.

- **The Go, reshaped (our own example; decided autonomously, the user's WAL-over-fsExt delegation).**
  The semantics are the same (whole-file, atomic, durable `Write`; failures retried; `Read` of a missing
  file `("", false)`), but only `os` functions the part already models are called: a `Write`'s
  temporary is the fixed `dir/.durable-<base>`, opened `O_RDWR|O_CREATE|O_TRUNC` (was `os.CreateTemp`,
  whose `runtime_rand` would be a new trusted model, and whose random names need a cofinite claim),
  written with one `WriteAt` (skipped when empty), synced, closed, renamed, the directory opened and
  synced; a `Read` is `tryRead`: `os.Open`, `Stat`, `make`, one `ReadAt` of the size (was
  `os.ReadFile`, whose `readFileContents` growth loop is untranslated). `errors.Is(err,
  fs.ErrNotExist)` stays. New premises the package doc states: no name of another file's temporary
  (`.durable-` prefix), a file of at most 1 GiB. A quick Go test (write, empty write, read back, one
  entry left in the directory) passed; not committed. The main tree's model
  (`TrustedCode/.../lib/durable.lean`) is unchanged but for its docstring's list of calls.
- **Project `durable` has a part `LinuxFs`** (`etc/goose.py`), with `path/filepath` and
  `internal/filepathlite` mapped to the part, no `LinuxFs/Code/...durable.toml` (every function
  translated). `etc/goose.py --check --project durable` passes.
- **The spec design (`Defs.lean`'s header).** Per file `f : DFile` (directory path `d`, its inode `J`,
  base `b`; `f.Ok`: clean absolute `d`, clean segments `b`, `.durable-b`). The client-visible state is
  `DurSt := {cur, alt}`: `cur` what `Read` returns, `alt = some old` while a `Write`'s rename may be
  lost to a crash. **A `Write` is two atomic updates** (`Write.spec`): at the rename `cur := data, alt
  := some cur`; at the directory sync's commit `alt := none`. Why not one (as `durableExt`'s): between
  the rename and the commit a crash may keep either contents, and no single point of the client's
  ghost state is right for both. Rejected: committing the client's update at the crash (helping, the
  update stored in `durInv`), which needs a saved proposition, a later stripped in the crash
  obligation, and the writer's `Φ` back through `savedPropOwn`'s `▷`-agreement; the two-update form
  costs the client only an `alt` it keeps in its own invariant (the tester: the WAL does not move
  during a `Write`, so both oracles are consistent with it). Masks: `durAuMask = osAuMask \ durN`, so
  the first update can be opened inside `os.Rename`'s `osAUnc` at the rename step (with `notCrashed`,
  to open `durInv`). **The mutex guards `True`** (`PkgInit.lean`'s fact `isMutex (globalAddr mu)
  True`): the calls are serialized in the proof by the caller's exclusive `durHandle γ f R`, not by
  `mu`, whose invariant is fixed at package init (before any claim exists) and whose ghost name a
  client's `durInv` could not agree with. kvdurable (concurrent callers) will need the handle in a lock
  of its own, or the token-in-`durInv` form (lock invariant a token, `durInv` holding `token ∨ handle`).
- **The invariant (`durInvBody`)**: the other half of `durSt`; the physical state `DurPhys` (half; the
  handle has the other): the claims' histories `hb` (on `.only [b]`) and `ht` (on `.only [tb]`), a
  commit lower bound `nc`, the candidates `cands` (inode, `OsMeta`, contents; `DCand.Ok`: size the
  contents' length, crash bounds `lo = hi = size`, as a synced file and a crash's `initMeta` both
  have); half of each claim, `osCommitLb nc`, half of every candidate's `osMeta`/`osBytes` (bytes
  `durB`). Facts (`DurOk`): every `K` keeping the entries of `hb` below `nc` leaves `b` (`valAfter`)
  as `OutOk` allows (absent iff `cur` or `alt` is, or a candidate holding `cur`'s or `alt`'s
  contents), stated without `RegionCrashed`'s `Follows` closure, which `b`'s history (renames only)
  does not need; `b` now holds `cur`'s candidate; the temporary is never a directory; `alt = none →
  hb.next ≤ nc`.
- **Next (in order):** (1) `tryRead`/`Read`: needs an `os.Open` of a present file in shared mode whose
  error is a `*PathError` of an errno other than `ENOENT` (`wp_osOpenFileS` does not export the
  semantics' `e = ENOENT → lookup = none`: a strengthened extension lemma, as `wp_osOpenDirS`'s), the
  `fi.Size()` interface call, `errors.IsPathErrnoNotExist.spec` (the WAL's hypothesis, to move from
  `wal/ExistCallees.lean` to `LinuxFs/Spec/errors/`); (2) `tryWrite`/`Write` (`os.OpenFile.wp_truncS`
  for an existing temporary, `specCreateTruncSnc` otherwise, `WriteAt`, `Sync`, `Close`,
  `Rename.specFileSnc` with the first update inside, `Open.wp_dirS`, `Sync.specDirS`, the second update
  after it); (3) `durInv_crash` (`crashRest_region` on the two claims with `osCommitLb nc`,
  `crashRestAt_take` of the candidate `b` holds) and the boot (`durBoot`, from the new generation's
  claims and the crash's `osFileStart`s); (4) `gen-init.py` (`LFS_PKGS`, `LFS_SPECIAL`: `init_Mutex
  True`) and `etc/gen-link.py` (a mode of its own or `--walfs`'s).

## W4c U4 log (branch `wal-u4`, 2026-11-14)

**The instance** (`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/RaftModel/`), one module per group:
- `Varint.lean`: minimal varints are prefix-free (`varintEnc_append_inj`) and short (`varintEnc_length_w64`).
- `Codec.lean`: canonical contents and their bytes. Snapshots: `walSnapCanon m` (`Index`/`Term` set, conf state
  nil iff zero, else set with `AutoLeave` set; no unknown fields; `Create`'s `snapC0` is canonical), bytes
  `snapEnc`; `walDecSnap`. Hard states: `WalHsC`, `hsEnc` (tags 1-3, then the unknown fields), `walHsCanon`
  (all nil when empty, as `&raftpb.HardState{}`; else all set, as raft's `hardState()`), `walDecHs`, bound 33
  bytes.
- `EntCodec.lean`: `walEntCanon` (`Term`/`Index`/`Type` set, `Data` nil iff empty), bytes `entryEncC` (the
  registered `raftpb.Entry`'s opaque encoder) below `2^48`, stand-in bytes above (ledger item 4); `walDecEnt`.
  Over two new part extracts (`etc/gen-part-copies.py`): `LinuxFs/Proof/go_etcd_io/raft/v3/PbContent.lean`
  (`EntryC`, `entrySize`) and `PbEntryType.lean` (`entDecode`, `EntWireOk`, `entryEncC`, and **`entryEncC_ok`, a
  copy of the main tree's axiom**: same name and statement; no new axiom). The script's `Extract` gained `bare`
  names (top-level declarations with their own binders).
- `Marshal.lean`: `walRaftMr : WalMarshal`, `walRaftU : WalUnmarshal`; proved `walRaftU_ok : walRaftU.Ok
  walRaftMr`, `walRaftU_snapCoh`, `walRaftMr_createOk : WalMarshalCreateOk walRaftMr`, `walRaftMr_encState_lt`.

**Per law** (the Link's hypotheses):
| law | status |
|---|---|
| `U.Ok`, `U.SnapCoh`, `WalMarshalCreateOk`, `Mr.encState < 2^32` | proved (`Marshal.lean`) |
| `NilLaw`, `ZeroLaw`, `MustSyncLaw`, `GetIndexLaw`, `GetTermLaw`, `WalHsOwn.{zero,getCommit,freeze}` | provable, not done: they need `P.hsIn`/`P.entIn`, whose form waits on the trust decision below (a frozen object at a canonical content with its hidden fields in an invariant, as `snapRoC`; for entries, the part copy of `entRoC`/`pbMsg`/`pbEntryC`/`pbEntryC_reg`) |
| `MarshalEntLaw` | provable after the part copies of `pbEntryC`, `pbEntryC_reg` (a copy of the main tree's axiom) and their vocabulary, with `isPkgInit pbutil` carried in `P.entIn` |
| `UnmarshalEntLaw`, `IsEmptyLaw` | blocked: no `isPkgInit` in the pre (ledger 2026-11-14, "the WAL's raftpb laws", item 1) |
| `MarshalHsLaw`, `CloneHsLaw`, `WalHsOwn.unmarshal` | blocked: `raftpb.HardState` has no trusted wire model (item 2; `CloneHsLaw`, `unmarshal` also item 1) |
| `WalHsOwn.reset` | blocked: `HardState.Reset` is names-only (item 3) |
| `WalDecEnvSupply` | not a law of these parameters (`errors.newVar`'s Perennial gap, §2) |

No law is false of real raftpb. `walPb_laws` (the bundle) waits for the blocked laws.

**Client obligation (C6 and the tester).** `Mr.encSnap`/`encState`/`encEntry` are the canonical forms' bytes, so
the objects a client passes must be canonical: raft's `hardState()` (all set) is, a zero hard state any form;
entries need `Term`/`Index`/`Type` set and `Data` nil iff empty (check the tester's and raft's literals;
otherwise change the canonical form, a choice internal to the instance).
