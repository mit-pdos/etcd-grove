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

