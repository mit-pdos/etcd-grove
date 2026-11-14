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

**Third session (branch `wal-u3c`, 2026-11-14): `hu` discharged; `hfo`'s invariant designed, its crash side proved;
`walBootCrash` not started.** No axiom, nothing trusted changed.
- **`hu` gone.** The replay of a closed set of logged operations is a tree only under the shared mode's disciplines
  (`TreeCut.lean`: without them it need not be, the §4.3 counterexample), and that theorem was proved (`closed_cut`,
  used by `machineCrash_initS`), but its conclusion was not kept for the next generation. Now `crashShared`
  (`GooseLang/Ext/Fs/CrashTok.lean`, untrusted) keeps `TreeWf st.fs.roots V'.now` (first conjunct; built in
  `os_local_crash` from `FsInit`), and **`crashRest_treeWf`** (`TreeShared.lean`, proof `TreeSharedCrash.lean`):
  `osSharedInv R -∗ crashRest … V' ={E}=∗ ⌜TreeWf R V'.now⌝ ∗ crashRest … V'`. `walInv_crash` takes no `hu` (it calls
  `crashRest_treeWf`; `uniqNames_of_wf`). The crash boot gets `TreeWf R V'.now` the same way (`NameOk`, `hjr`).
  **Merge note:** a proof destructuring `crashShared`'s pure part gains a first component (two sites, fixed).
- **`hfo`: condition checked, design (ledger 2026-11-14, "`hfo` not derivable").** `walAreaRes` is unpacked by no
  client (outside `wal/` only comments and the WAL's own `Spec` files name it); its body is exposed (not
  `@[no_expose]`): sealing it formally means `import all` in its WAL proofs (a follow-up, not needed for the check).
  The crash side is proved (`BootFilesOnly.lean`): `HistNoDir h b` (no version of the history holds a directory at
  `b`), `regionCrashed_noDir`, `regionCrashed_filesOnly` (a directory all of whose names crash-kept claims cover with
  `HistNoDir` holds only files after the crash), `HistNoDir.log`. `hfo` narrows to WAL names and `nm.tmp`: the
  `nm.broken.<t>` directories need only `SubCover`, which the boot's whole claims give (all directories reachable
  under the name, tagged with it). The invariant side (a framed conjunct `walFoRes`: claims `fl` at half, `HistNoDir`
  of `fl` and of the WAL-directory claims, coverage of every area version's directory at a WAL name or `nm.tmp`), by
  the updates under the new claims, each to become an invariant step:
  1. the pipeline's `0.tmp`/`1.tmp` (`tmpClaim`): `filePipeline.alloc`'s create (`specCreateS` → `specCreateSnc` with
     the invariant's half, the os specs are shaped for it), the pipeline's removal of its leftover, `cut`'s rename
     (already an invariant step; its source half now the invariant's too), the hand-off (`walParked` ↔ the handle:
     `openAtIndex`, `Close`, `CloseHandle`, `WAL__CloseOpening`, `CreateHandle`, `CreateUnmint`): ~15 proofs;
  2. `Create`'s `nm.tmp`: the `mkdir` (an area step: the new directory's claim's half into `fl`), `TouchDirAll`'s
     `.touch` probe (fileutil's spec takes `osSubtree` whole: needs an AU-shaped spec, a fileutil spec change),
     the first segment's create, `os.RemoveAll(nm.tmp)` of a leftover (needs an AU-shaped `os.RemoveAll` spec, a new
     os spec and proof), the rename `nm.tmp` → `nm` (the claims become the WAL directory's);
  3. `Repair`'s lent names (`lendKey`): its `.broken` file's create, rename;
  4. the WAL-directory claims' `HistNoDir`: every invariant step logging into one proves its new version files-only
     (segments and `walOthers`): `cut`, `Create`'s commit, `Repair`, `renameWAL`;
  5. **open point**: `cleanupWAL` (`wal-create25`) renames `nm` → `nm.broken.<t>`: until that rename is committed a
     crash may keep the version with `J` at `nm`, so `J`'s claims must stay covered (the invariant's half in `fl`), but
     `walAreaRes`'s `areaCls` holds `nm.broken.<t>`'s subtree claims whole (for `os.RemoveAll`). Either coverage is
     released only past the commit bound (`n`), the broken directory's claims staying split until a sync, or
     `walAreaRes` takes the broken subtrees at less than whole.
  **Estimate 3-5 sessions; cheaper alternative for 2 (for the coordinator):** drop `TmpOk` for a general-subtree
  `os.RemoveAll` spec (`SubCover`, which the boot gives) and let `tmpClTouch` accept a directory `.touch` (the probe's
  `O_CREAT` open fails with `EISDIR`, `Create` returns the error): then only `nm` (1, 3, 4) needs `fl`, and none of the
  AU-shaped fileutil/`RemoveAll` specs.
- **`walBootCrash`, started (pure).** `BootCrashCl.lean`: `bootWals m jr` (the area's WAL names holding a directory,
  with it), `mem_bootWals`, `bootWals_nodup`, `bootWals_fun`, `bootWals_inj` (unique naming: distinct directories),
  `bootWals_ne_root`, `bootWals_nameOk`, `bootWals_mem` (`TreeWf`): the facts `hdirs1`/`hJm`/`hnames`/`hnok` rest on.
  Next: the claim list over `bootWals` (the `osNames_split`s of the area's and each `J`'s whole claims), then the
  proof as designed in the second session, with `hfo` (narrowed) its premise until `walFoRes` lands.

**Second session (branch `wal-u2b`, 2026-11-14): `tryRead` and `Read` proved; the package initializer
generated.** No axiom, no trusted change, no `sorry`. `Read.wp_proof` takes `tryRead.spec`;
`tryRead.wp_proof` takes `errors.IsPathErrnoNotExist.spec` (the WAL's hypothesis, still unproved: it
waits on Perennial's `errors-facts` branch) and the `os` specs `File.Stat`, `fileStat.Size`,
`File.ReadAt`, `File.Close` (proved in the part).

- **The Go: `errors.Is(err, os.ErrNotExist)`** (was `fs.ErrNotExist`, the same variable's value in Go):
  the WAL's hypothesis is stated of `os.ErrNotExist`'s variable (`os`'s package fact gives its
  points-to), so no second hypothesis for `io/fs`'s; `io/fs` is no longer imported. Retranslated
  (`etc/goose.py --project durable`; the main tree's trusted translation is unchanged).
- **`Open` of a present file never fails with `ENOENT`**: the extension lemma `wp_osOpenFileSN'`
  (`GooseLang/Ext/Fs/TreeSharedOpenFileN.lean`, untrusted, a new module so that nothing rebuilds:
  `wp_osOpenFileS'`'s proof with the semantics' `ENOENT` premise used in its failure branch) and the
  `os` lemmas `OpenFile.wp_fileSN`/`Open.wp_fileSN` (`LinuxFs/Proof/os/NsFileS.lean`, the errno explicit
  as `os.errnoPathErr err e`, `e ≠ ENOENT`).
- **Defs changes (internal):** `durHandleP γ f R p` (the handle at a physical state; `durHandle` is
  `∃ p, durHandleP`), `DurPhys.CurIs f p v` (what the name holds under `p`), `DurOk.inj` (the
  candidates at distinct inodes, so `cur` is determined by `p`), `DCand.Ok`'s `length ≤ 1 GiB` (one
  `ReadAt`; `Write`'s `data` bound, so the write proof keeps it).
- **`tryRead.spec`** (`LinuxFs/Spec/.../durable/tryRead.lean`, internal): at the handle's `p`, with `∃ s,
  DurOk f s p` as a premise (read off the invariant by the caller at a step), `isPkgInit os`; when
  `done`, `(s, ok)` is what the name holds (`CurIs`). Nothing changes, so no update in it.
- **`Inv.lean`**: `DurOk.curIs`, `DurPhys.curIs_unique`, `durInv_open` (with `notCrashed`),
  `durInv_okAt`/`durInv_okHandle` (the facts of the handle's `p`), `durInv_readAU`/`durInv_readHandle`
  (a read's update committed at a step: `s.cur` is what the name holds), `curRes_file`/`curRes_none`.
- **`Read`**: the mutex taken (`mu_of_pkgInit`, `PkgInit.lean`), `tryRead` retried (`wp_for`); before
  each attempt, at a step (`wp_notCrashed_acc`), `durInv_okHandle`; after a done one, at the next step,
  `durInv_readHandle` commits the client's update; the deferred `Unlock`.
- **The package initializer**: `etc/gen-init.py` (`LFS_PKGS`, `LFS_SPECIAL`: `sync.init_Mutex True`),
  `LinuxFs/Proof/.../durable/Init.lean` generated; `--check` passes.
- **Not done:** `errors.IsPathErrnoNotExist.spec` still lives in
  `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/ExistCallees.lean`, which `tryRead`'s proof imports
  (moving it to `LinuxFs/Spec/errors/` rebuilds the WAL's importers: do it when Perennial's
  `errors-facts` proves it). No `etc/gen-link.py` mode yet (the plan: lines `durable_tryRead: ...` /
  `durable_Read: durable_tryRead` in `--bboltfs`'s list, or a mode of its own; `errors.IsPathErrnoNotExist`
  a pending hypothesis).
- **Next (in order):** (2) `tryWrite`/`Write`: `tryWrite`'s spec at the handle's `p` with the first
  update inside, as `tryRead`'s (premise `∃ s, DurOk f s p`; post: `false` with the handle at some `p'`
  and the first update not yet committed, or committed; `true` with the second committed). The
  invariant cases: the temporary's inode is never a candidate within a generation (needs a fact
  `tmp ∉ cands` in `DurOk`, from `tmpRes`'s whole `trFile`, or derived from the resources); a retry after
  a rename makes a fresh candidate (`O_CREAT`, the temporary absent) with `data`, so `cands` grows
  and `alt` stays. (3) the crash and boot lemmas; (4) the link.
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

No law is false of real raftpb. `walPb_laws` (the bundle) waits for the blocked laws (superseded below, U4 b).

**Client obligation (C6 and the tester).** `Mr.encSnap`/`encState`/`encEntry` are the canonical forms' bytes, so
the objects a client passes must be canonical: raft's `hardState()` (all set) is, a zero hard state any form;
entries need `Term`/`Index`/`Type` set and `Data` nil iff empty (check the tester's and raft's literals;
otherwise change the canonical form, a choice internal to the instance).

## W4c U4 b log (branch `wal-u4b`, 2026-11-14)

**Decisions** (the coordinator's, recorded in the ledger 2026-11-14, "the WAL's raftpb laws"):
- **Package initializations in the laws' pres** (item 1): `isPkgInit pbutil` in `MarshalEntLaw`'s and
  `MarshalHsLaw`'s, `isPkgInit proto` in `CloneHsLaw`'s, the part's `isPkgInit raft` in `IsEmptyLaw`'s,
  `isPkgInit wal` in `UnmarshalEntLaw`'s and `WalHsOwn.unmarshal`'s (wal functions, as every wal spec);
  `WAL.saveState.specPre` (`cut`'s) gains `isPkgInit wal`. Repairs: `saveState`/`Save` take the handle's
  `isPkgInit wal` out (`walHandleIn_pkgInit`, `SaveHandle.lean`), `cut` frames its `Hwpk`.
- **The part's raft root fact** is `rootInit`: `emptyState`, the main tree's conjunct word for word
  (`LinuxFs/Proof/go_etcd_io/raft/v3/PkgInit.lean`; its `wp_initialize'` generated, `etc/gen-init.py`'s
  `LFS_SPECIAL`, the main tree's steps).
- **`raftpb.HardState`'s registration and `HardState.Reset`'s model stay out** (the user's call): four
  laws stay hypotheses of the closed result (`notes/wal-fsext-plan.md` §10, "The raftpb instance's laws
  pending the user", with what registering would take).
- **Part extracts** (`etc/gen-part-copies.py`, copies of existing main-tree declarations and of one
  main-tree axiom, `pbEntryC_reg`): `InvPb` (`pbMsg`, `pbMsg_alloc`), `PbContent` (+ `optCell`, `bytesC`,
  `entRoC`), `PbContentOwn` (`entPtsCC`), `PbEntryType` (+ `entryTree`, `pbEntryM`, `pbEntryC`, its simp
  lemmas, `entPtsCC_freeze`, `pbEntryC_reg`). The script: a `set_option`/`omit ... in` prefix joins its
  declaration; an extract keeps the source's order (sections around top-level declarations; `pre` ones
  first), with the source section's variables.

**The instance's objects** (`RaftModel/Pb.lean`; internal choices):
- `P.entIn l e := entRoC l (walEntCanon e) ∗ ⌜walEntSmall e⌝`: the frozen registered entry at the canonical
  content.
- `P.hsIn p h := ⌜p = null ∧ h = hsZero⌝ ∨ ∃ c, hsRoC p c ∗ ⌜c.model = h ∧ (hsEmptyP h ∨ c = walHsCanon h)⌝`:
  **an empty hard state at any content** (changed from the canonical one: the tester's `toHS` of a zero
  state sets the three cells, raft's `emptyState` leaves them nil; an empty state is never marshalled).
  `hsRoC` = the frozen cells (`hsCells`) and raft's `pbMsg raftpb.HardState` invariant.
- `HsO p h := hsOwnC p (walHsCanon h)`: owned cells and hidden fields (`WalHsOwn.zero` has no update to
  allocate an invariant with; `freeze` allocates `pbMsg`).
- **Stand-in entry bytes** (`EntCodec.lean`, ledger item 4): now `2 ^ 64` bytes or more (was `2 ^ 48`),
  longer than any slice, so bytes in memory that `walDecEnt` decodes are the real encoding
  (`walDecEnt_small`): `UnmarshalEntLaw` needs it.

**Per law** (supersedes the U4 table):
| law | status |
|---|---|
| `U.Ok`, `U.SnapCoh`, `WalMarshalCreateOk`, `Mr.encState < 2^32` | proved (U4, `Marshal.lean`) |
| `NilLaw`, `ZeroLaw`, `MustSyncLaw`, `IsEmptyLaw` | proved (`LawsHs.lean`; `IsEmptyLaw` over `rootInit`) |
| `GetIndexLaw`, `GetTermLaw`, `MarshalEntLaw`, `UnmarshalEntLaw` | proved (`LawsEnt.lean`, over `proto.MarshalPb.spec`/`UnmarshalPb.spec` at `pbEntryC_reg`) |
| `WalHsOwn.zero`, `getCommit`, `freeze` | proved (`LawsHs.lean`) |
| `MarshalHsLaw`, `CloneHsLaw`, `WalHsOwn.unmarshal`, `WalHsOwn.reset` | **hypotheses** (no trusted model of `raftpb.HardState`; [user]) |
| `WalDecEnvSupply` | not a law of these parameters (§2) |

The bundle: `walPb_laws : WalPbLaws walRaftP walRaftMr walRaftU` (`RaftModel/Laws.lean`) and
`walRaftHsO_own h_unmarshal h_reset : WalHsOwn walRaftP walRaftU walRaftHsO`.

**The client literals against the canonical forms** (task 4):
- The tester (`examples/etcd/wal/wal.go`): `toRaft` sets `Index`, `Term`, `Type` (`EntryNormal.Enum()`), and
  `Data = entData(e)`, non-nil and of at least 16 bytes: canonical. `toHS` sets the three cells: canonical
  when non-empty; a zero state is not canonical, hence the relaxed `P.hsIn` above.
- Raft: `hardState()` (`raft.go:504`) sets the three cells: canonical; `emptyState` (all nil): an empty state.
  **Raft's entries are not canonical**: `appendEntry` sets `Term`/`Index` on a clone of the proposal, whose
  `Type` is nil for a normal entry (`raft.go:979`'s `&pb.Entry{Data: nil}`, `node.go:472`'s proposals) but set
  for a conf change (`bootstrap.go:61`) and for `raft.go:1359`'s replaced proposals (`EntryNormal.Enum()`);
  entries a follower appends come off the wire with the leader's presence. **No canonical form fits both
  the tester and raft**: `Mr.encEntry` is a function of the model only. For C6 the WAL's marshaller
  parameter must speak of contents (`encEntry` over `EntryC`, or `P.entIn` carrying the content and `Save`'s
  stream over it) -- a statement change of the WAL's specs, deferred to C6. The canonical form stays the
  tester's (`Type` set).


## W4c U1 log (branch `wal-u1`, 2026-11-14)

**The tester is in the part, translated and with its pure proofs; nothing over the new WAL specs yet.** No
axiom, no `sorry`, nothing trusted changed. `TP/` = `LinuxFs/Proof/github_com/mit_pdos/etcd_grove/examples/etcd/wal/`.

- **Translation** (`etc/goose.py`, project `etcd-wal`'s new part `LinuxFs`): `LinuxFs/{Code,GeneratedProof}/
  github_com/mit_pdos/etcd_grove/examples/etcd/wal.lean`, over the part's `os`, `wal`, `walpb`, `fileutil` and
  `lib/durable` (raftpb, zap, `strings`, `primitive`: the main tree's/Perennial's). **`purgeRound` translated with
  its body** (no `LinuxFs/Code/.../etcd/wal.toml`; the main tree's names-only `!purgeRound` and its approved axiom
  stay main-tree only): the body adds no trust; U6 decides whether it stays. `--check` passes.
- **Package init**: `TP/PkgInit.lean` (the main tree's `Base.lean`: fact `True`), `TP/Init.lean` generated
  (`etc/gen-init.py`, `LFS_PKGS`; `--check` passes).
- **Pure proofs, copied** (55 modules, all build): `TP/Defs.lean` = the main `Defs.lean`'s `section pure` **minus
  `tOracleFile`** (over `durableExt`'s `DurableState`); `Rep`, `RefLemmas`, the 25 function proofs of `ref.go`/
  `oracle.go` and their 25 specs (`LinuxFs/Spec/.../etcd/wal/`) unchanged but for imports; `TP/CrashPure.lean`
  (`tCandOk_crash`, `tPreOk_crash`, the pure half of `Crash.lean`: the `fsExt` WAL's `walStCrash` is
  `absDisk_semantics.crash`, so they apply as they are). The copies are plain files, not `gen-part-copies.py`
  output: from now on the part's are the tester's proof, the main tree's are frozen until U8 deletes them.
- **Left for U5 (not copied)**, with what each needs:
  - `Defs.lean`'s `tOracleFile`: restate over `lib/durable`'s client state (`DurSt` `{cur, alt}`: the oracle file
    holds `tEncodeOracle o`, or none and `tFreshOracle`, for `cur`, and for `alt` while a `Write` is pending);
  - `TInvBody`/`TInv`/`TBoot`: `durableOwnM`/`durableReserved` → U2's `durInv`/`durHandle`; `walDirIs`/
    `walSyncedLb`/`walNamed` → the part's (`walPast`, `walSyncedLb`, `walNamed`); `walArea` → `walAreaOk`/
    `walAreaRes`; `dirDurable root`, `dirDurable (tArea root)` → U3's area-a-root (`DirsRoots`); the lock token
    and `osCallPerm 1`/`½` threaded (§2); `tRelI` unchanged in shape;
  - `Crash.lean`'s `tester_crash`: over `walInv_crash` + `walBootCrash` (U3) and `durInv_crash`/`durBoot` (U2),
    with `CrashPure`'s lemmas for the oracle;
  - `PurgeBody.lean`, `purgeRound.lean` and its spec: over `absDiskExt`'s `"WalPurge"` step; no `fsExt` statement
    without the lock model (U6);
  - `absSnapMd` (in the copied `Defs`): the new `walSnapAt` requires `c.model = md`, the old constrained only the
    index, the term and whether the conf state is set; the tester's conf state is `{Voters: [1]}`, so `absSnapMd`
    becomes `⟨⟨[1], [], [], [], false⟩, idx, term⟩` (`RefLemmas` reads only its `Index'`/`Term'`).
- **Mismatches found** (for U5/U7; each a change to our own example's Go, so a change of the closed theorem's
  statement: the user's at U7's hard stop):
  1. **The paths against U3's boot premise 3 (the area a root).** The tester's area is `root/data/member`
     (`tArea`), the oracle `root/oracle/state`. With the area an `fsExt` root, `root` cannot be one (`RootsOk`:
     no root under another), so `root/oracle` is a second root (`durable` never creates a directory). Then
     `Boot`'s first start, `TouchDirAll(data)` and `TouchDirAll(memberDir)` (`wal.go:617`), has no spec: `data` is
     above a root (its `.touch` probe is an `O_CREAT` open there, stuck: `fsExt` opens only `O_RDONLY` above a
     root) and `memberDir` is the root (the part's `TouchDirAll.spec` creates an absent `parent/name`; its probe's
     `.touch` in the area is under the WAL invariant's area claim, `walBoot0` giving back only names holding an
     entry at boot). Proposed: drop both calls (the area and the oracle directory are the environment's, as the
     roots are), `Boot(area, orDir, …)` taking the two roots. The other boot facts hold: the oracle and its
     temporary `.durable-state` are outside the area; the WAL name `wal` is `NameOk`; `Create`'s metadata `"m"` is
     non-empty and short.
  2. **The oracle's size against `durable.Write`'s 1 GiB premise.** The candidates' histories (`c.h`) are
     whole histories since `Create`, so `tEncodeOracle o` grows without bound across incarnations; `durableExt`
     had no bound. Proposed: the tester stops (`StatusDown`, before the `storeOracle`) once the encoding would
     exceed `2^30` bytes, or the closed theorem bounds the incarnations.
  3. **`SaveSnapshot`'s conf state against U4's canonical form.** `wal.go:373`'s `&raftpb.ConfState{Voters:
     []uint64{1}}` leaves `AutoLeave` nil; `walCsCanon` has it set (as raft's `ProgressTracker.ConfState()`
     sets it), so `walSnapAt`'s `snapEnc c = Mr.encSnap md` fails. Proposed: the tester sets `AutoLeave:
     new(bool)` (keeping the canonical form raft's, which C6 needs). Entries (`toRaft`) and hard states (`toHS`)
     fit (U4 b log); `Open`'s `walpb.Snapshot{Index, Term}` needs only `walSnapIdTerm`.
  4. **For C6, not the tester:** real etcd's member directory holds `snap/` beside `wal/`, a name `AreaSlot`
     covers, so U3's `hslots` (and the area claim) do not fit the server's layout with the area at `member/`.

## W4c U5 log (branch `wal-u5`, 2026-11-14)

**First session: the tester's invariant and first boot over `fsExt`, `storeOracle`/`loadOracle` proved; no member
operation yet.** No axiom, no `sorry`, nothing trusted changed, no Go changed. `TP/` as in the U1 log; specs in
`LinuxFs/Spec/.../examples/etcd/wal/`.

- **`TP/Inv.lean`** (decisions mine, internal):
  - `TEnv` = `root`, the roots `R`, the area's directory `jr`, the oracle directory's `jo`. The area `tArea root` and
    `tOrDir root` (`root/oracle`) are **two roots of `R`** (U3's premise 3; U1 mismatch 1 stands: `Boot`'s
    `TouchDirAll(data)`/`TouchDirAll(memberDir)` have no spec there; held for the user). `TEnv.orFile` the
    `DFile ⟨tOrDir root, jo, "state"⟩`; `tOrPath_child`: its name is `tOrPath root`.
  - `tOracleFile s o oa` over durable's `DurSt`: `cur` holds `o` (`tOrHolds`: its encoding, **at most 1 GiB**,
    `tOrSmall`; or no file and the fresh oracle), and `alt = some v` iff `oa = some o'` with `v` holding `o'` (the
    oracle before a pending `Write`). Lemmas `_alt`, `_write` (the rename's update), `_sync`, `_fresh`, `_crash`
    (a crash's file, `cur` or `alt`'s, holds one of the two oracles: for `tester_crash`). The 1 GiB bound is
    `durable.Write`'s premise (U1 mismatch 2: whether the tester meets it is still open, so `storeOracle.spec`
    takes `tOrSmall o'`) and gives `decodeOracle` its length bound (the W4c handoff's open question 2: settled this
    way, an internal invariant).
  - `TInvBody e γ` (ghost names `TGS`: durable's `DurGS`, `γo` holding `(o, oa)`, `γw` holding `od`): `durSt γd s`,
    `tOracleFile s o oa`, the ghost halves, `WalFs.walDirIs (tWalDir root) od`, `tRelI root o od` (as the main
    tree's, over `WalFs.walSyncedLb`/`walNamed`) and **`tRelA root oa od`** (the pending oracle's relation: a crash
    during a `Write` may keep the old file; the WAL does not move during a `Write`). `TInv` is a **plain invariant**
    (not `body ∨ crashed ∗ tok`): the client cannot refute `crashed` inside durable's/the WAL's atomic updates (no
    `notCrashed` there), so the crash obligation must open it and close it with its contents (the `_keep` lemmas,
    as the main tree's `tester_crash`). The main tree's `dirDurable root` and the conditional `dirDurable (tArea
    root)` are gone (the area is a root, durable from the first boot); `durableReserved` has no counterpart.
  - `TBoot e` (the incarnation's precondition **after** the shared mode's switch; how the program reaches
    `wp_osShare` before its first `os` call, inside `loadOracle`, is U7's): `∃ W γ o od`, `TInv`, `tOrOwn γ o none`,
    `tWalOwn γ od`, `walAreaOk walCodec walRaftMr R jr (tArea root)`, `dirDurable (tArea root)`, `walAreaRes jr`,
    `walUnlockedTok`, `durInv`, `durHandle`, `osCallPerm 1`, and the crash tokens the crash obligation takes
    (`walCrashTok`, `durCrashTok`; `fsSQ_crash_adequacy`'s obligation is produced with the WP from `P L`, so it can
    hold them). `ownGoState`/package init not included (U7).
- **`walBoot0` now exports `walOwn ∅`** (`S/BootStart0.lean`, `S/Boot0.lean`; statement changes, no other importer):
  it dropped `walGhost_init`'s program map, so a client had no `walAbsent dir` for `Create`'s update. **Merge note
  for `wal-u3d`**: `walStart_boot0`'s conclusion gained `∗ walOwn (W := W) ∅` (last), `walBoot0`'s `∗ walOwn
  (W := W) ∅` after `walPast`.
- **`TP/Boot0.lean`, `tBoot0`** (proved): from `wp_osShare`'s outputs, `TBoot e`, over `walBoot0` and **`DurBoot0`, a
  hypothesis (U2's durable first boot, not landed)**: from the whole claim on the file's directory (a root of `R`,
  neither `f.b` nor `f.tb` present, nothing logged), `|={E}=> ∃ γ, durInv γ f ∗ durHandle γ f R ∗ durSt γ ⟨none,
  none⟩ ∗ durCrashTok γ`. U2c may prove a finer form (the two `.only` claims) and derive this one. World premises
  (U7): `RootsOk R`, the two roots, `jo ≠ jr`, both in `V.now`, `hslots`, no oracle file nor temporary,
  `ReceiptBoundLe GF (2^62)`, `e.orFile.Ok`.
- **`absSnapMd`** = `⟨⟨[1], [], [], [], false⟩, idx, term⟩` (`TP/Defs.lean`; `RefLemmas` unaffected). The model reads a
  nil `AutoLeave` and a set `false` alike, so the invariant fits either Go form; whether `wal.go:373`'s object
  encodes canonically (`snapEnc c = Mr.encSnap md`, U4's `walCsCanon` sets `AutoLeave`) is an obligation of
  `saveSnap`'s proof, not of the invariant: U1 mismatch 3 (the Go `AutoLeave: new(bool)`) still held for the user.
- **Proved** (`TP/storeOracle.lean`, `TP/loadOracle.lean`): `storeOracle.wp_proof` (from `encodeOracle.spec` and
  `durable.Write.spec`): the rename's update (`tOracleFile_write`, ghost `(o', some o)`, `tRelI o'` the caller's,
  `tRelA (some o)` the old body's `tRelI o`), the sync's (`tOracleFile_sync`, ghost `(o', none)`); `tN_sub_durAu`.
  `loadOracle.wp_proof` (from `decodeOracle.spec`, `freshOracle.spec`, `durable.Read.spec`): the read's update
  commits unchanged and gives `tOrHolds s.cur o`; no panic. **Stated, not proved** (callee hypotheses, pure Go):
  `encodeOracle.spec`, `decodeOracle.spec` (on `tEncodeOracle o` with `tOrSmall o`: `(v, true)`), `freshOracle.spec`.
- **Next (in order):** a member representation (`memberRep`: `m.o` the program's oracle `o`, `m.w` the open handle
  `walOpenWF walRaftP walRaftMr w (tWalDir root)` or nil, the raft-like fields; with `TBoot`'s resources), then
  `member.sync`/`close` (WAL `Sync`/`Close` + `storeOracle`, `tRelI` re-established from the new `walSyncedLb`),
  `save`/`saveSnap` (the WAL AU committed in `TInv`: `walDirIs` with `tWalOwn`; `toRaft`/`toHS` against
  `walRaftP`; `saveSnap`'s `walSnapAt` needs mismatch 3 decided), `opOwnSnap` without the purge (U6), `restart`
  (`restartRead`: `ValidSnapshotEntries`, `Open`, `ReadAll`, `Repair`; `checkRestart`), `Boot` (the `Create` arm:
  `walAbsent` from `TBoot`'s `od = none`), and `encode/decodeOracle`; `tester_crash` once U2c's `durInv_crash` and
  U3d's `walBootCrash` land (over `tOracleFile_crash`, `CrashPure`, the WAL `_keep` lemmas).
