# W4c U5, item 2: the tester's crash, `tester_crash` and `tBootCrash` (branch `wal-c-tcrash`, 2026-11-14)

Base `origin/wal-int` (`87ead66a41`). No axiom, no `sorry`, nothing trusted changed, no Go changed, no statement
of an existing lemma or spec changed: two new modules only. `TP/` = `LinuxFs/Proof/github_com/mit_pdos/etcd_grove/examples/etcd/wal/`.
`#print axioms` of both theorems: `propext`, `Classical.choice`, `Quot.sound`, `recEncC_ok` (the WAL codec's
existing axiom, which `tBoot0` also rests on).

## Proved (`lake build` of both modules passes)

- **`TP/BootCrash.lean`**:
  - **`TCrashed e V`** (generation `L`, first tree `V`): what the crash obligation hands the new generation
    besides `osTree … e.R V`. It holds:
    - the WAL's start from `walInv_crash`: `walStart … s V.now`, the boot files (`trFile`), `walUnlockedTok`,
      `walCrashTok`;
    - the ghost WAL state `od`, which the new program map holds (`walDirIs W (tWalDir root) od`), and the oracle
      `o` that accounts for it (`tRelI W root o od`);
    - `dirDurable W (tArea root)`;
    - the oracle file as the crash left it (`durFound`/`durFoundTmp` at `v`), with `tOracleFile ⟨v, none⟩ o none`;
    - the pure facts that `walBootCrash` needs: `V.2 = []`, `WalsBounded s`, `DirsRoots R s`, `TreeWf R V.now`,
      and **`BootFo V.now jr`**.
  - **`tBootCrash`** (modelled on `tBoot0`): `TCrashed e V -∗ osInv -∗ osSharedInv R -∗ osCallPerm 1 -∗`
    (every directory's whole claim) `={E}=∗ TBoot e`. Its steps:
    - `walBootCrash` gives the area (the `bootOthers` claim it returns is dropped);
    - `claims_take` picks the oracle directory's claim from `bootRest` (`mem_bootRest_root`);
    - `durBoot` on that claim gives durable's invariant, handle, state `⟨v, none⟩` and crash token;
    - the tester's ghost variables `(o, none)` and `od`, and `TInv`, are allocated.

    World premises, as `tBoot0`'s (U7): `RootsOk R`, the area and the oracle directory two distinct roots,
    `ReceiptBoundLe GF (2^62)`.
- **`TP/Crash.lean`, `tester_crash`**: `TInv (L, W) e γ -∗ walAreaOk -∗ dirDurable W (tArea root) -∗ durInv -∗
  walCrashTok W -∗ durCrashTok -∗ crashed -∗ crashRest Q L L' [] false V' ={⊤}=∗ osTree (L') e.R V' ∗ TCrashed (L')
  e V'`. Its inputs are the persistent parts and crash tokens of the old `TBoot`, which the program's crash
  condition keeps, and `fsSQ_crash_adequacy`'s crash resources. Like the main tree's, it opens `TInv`, cannot
  refute the crash, and closes it again with its contents. Its steps:
  1. **The WAL's crash first** (`walInv_crash`, `D = []`), at `⊤ \ tN`.
  2. **Durable's crash** (`durInv_crash`) with the WAL's `D'`. Its `hD` holds by `durCrash_hD` and the new pure
     lemma **`inAreaDir_not_orDir`**: by unique naming, a file named in a directory under the area is named
     outside the oracle directory, since that directory is a root and no entry names it (`TreeWf`, which
     `walInv_crash` exports). So the WAL-first order needs nothing more.
  3. `crashRest_treeS` gives the new tree.
  4. `tOracleFile_crash` and **`tRel_crash`**: the oracle the crashed file holds is `o` or the pending `oa`, and
     either one's relation is in the invariant.
  5. `dirDurable_crash_keep`, then **`tWal_crash`**: the WAL state across the crash, by phase. This is the main
     tree's case split over the part's `_keep` lemmas (`WalFs.walDiskAt_crash_keep`, `walAbsent_crash_keep`,
     `walDiskAt_crash_any_keep0`), with `CrashPure`'s `tCandOk_crash`/`tPreOk_crash`.
  - Masks: `walN_sub_tN`, `durN_sub_tN`, `osShN_sub_tN`.

## The open question: how the new generation gets `walSyncedLb`/`walNamed` back

The answer is the crash view (`walCrashWal W W'`, returned by `walInv_crash`), not `walStart`/`walPast`. Given the
old generation's `walSyncedLb W dir (tCandMark o c)` and `walNamed W dir` (from the old `tRelI`),
`WalFs.walDiskAt_crash_keep` returns:
- the crashed state, an image of `d.H` at the candidate's mark;
- the new program map's `walDirIs W' dir (some d')`;
- `walSyncedLb W' dir n` and `walNamed W' dir`.

So `tRelI W'` is rebuilt with the same candidate. The new generation's `walPast W' s'` is not needed: TBoot has
no `walPast`, and `dirDurable` comes from `dirDurable_crash_keep`. The crash view is consumed once, by the WAL
directory's `_keep` lemma, which is fine because the tester has one WAL directory.

## Hypotheses / premises

- **`hfo : BootFo V'.now e.jr`** is a premise of `tester_crash`, carried in `TCrashed` to `walBootCrash`. As
  `boot.md` says, it is not derivable until `walFoRes` lands. When it lands, `walInv_crash` should export it and
  the premise goes, with no change to `TCrashed`/`tBootCrash`. Until then it blocks a closed result: the
  adequacy theorem's crash obligation is `∀ L' V'`, and nothing discharges this premise.
- `hQ : ∀ st st', Q st st' → W1 walCodec st st'` (`walInv_crash`'s, the crash premise of the closed theorem),
  `hPre : AbsDiskGpreS GF`, and `ho : (tOrDir root, jo) ∈ R` (a world premise).
- No new hypothesis spec, no ledger entry (no statement was false).

## For U7 (how these plug into `fsSQ_crash_adequacy`)

- The new generation's `P L'` is `osInv ∗ osTree e.R V' ∗ TCrashed e V'` for some `V'`. The obligation gives
  `osInv L'`, and `tester_crash` gives the rest.
- The program's first `os` call does `wp_osShare` with that `V'`. `tBootCrash` then gives `TBoot e`.
- The old `TBoot`'s `walAreaOk`, `dirDurable`, `durInv`, `TInv` (all persistent) and its two crash tokens must be
  set aside by the program's WP for the crash obligation. The program never uses the crash tokens.

## Decisions for the user

None reached.

## Next

- `walFoRes`, which discharges `hfo` (not started here, as instructed).
- U7: the per-generation `P`, and the closed theorems (a user decision).
