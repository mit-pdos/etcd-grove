# W4c U3: the crash boot, `walBootCrash` (branch `wal-c-boot`, 2026-11-14)

Base `origin/wal-int` (`8fdd224baa`), merged again with `origin/wal-int` after `wal-c-durable` landed there.
No axiom, no `sorry`, nothing trusted changed, no Go changed. `S/` = `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/`.

## Proved (`lake build` of each module passes)

- **`S/BootCrash.lean`, `walBootCrash`**: the crash boot. Run in the new generation right after its
  `wp_osShare` (with `V` the crashed history, nothing logged by `crashRest_treeS`), from `walInv_crash`'s
  outputs. It takes `osInv`, `osSharedInv R`, `walStart L W C Mr R jr r s V.now`, the boot files
  `[∗list] i ∈ bootFiles V.now jr, trFile i False`, and the whole claim of every directory of `V.now`.
  It gives `walAreaOk C Mr R jr r ∗ walAreaRes jr`. It hands back the area's claim on its names that are
  no `AreaSlot` holding an entry (`(.except []).inter (bootOthers V.now jr)`), and the whole claim of
  every directory not taken (`bootRest V.now jr`; another root's directory, such as the oracle's, is
  among them: `mem_bootRest_root`). The client frames the rest itself: the lock token, the crash token
  and `walPast` come from `walInv_crash`, and `osCallPerm 1` from the program. The tester (U5) and C6
  consume it in this form.
  Premises:
  `hV : V.2 = []`, `hR : RootsOk R`, `hr : (r, jr) ∈ R`, `hwf : TreeWf R V.now`, `hbd : WalsBounded s`,
  `hdr : DirsRoots R s` (all given by `walInv_crash` or the first boot's world premises), **`hfo : BootFo V.now jr`**
  (below), `hrb : ReceiptBoundLe GF (2^62)`, `henc` (U4's law). `DirsAvoid`/`DirsOk` come from `DirsRoots`.
- How the claims are split (`walInv_alloc`'s `cl = bootCl V jr`):
  - the area's claim on `bootN` (every name except the WALs' names and the names given back);
  - each WAL directory's claim on its non-pipeline names (`walDir_boot`; its `0.tmp`/`1.tmp` claims go
    to `walTmpsRes` with their files);
  - each WAL name's own `.only [nm]` claim.

  `Jm = bootJm` maps each WAL's path to its directory. `walOthersL` is built from the boot files.
  `walAreaRes` gets the other half of the area claim, plus the whole claims of every directory under
  an `nm.<sfx>`, each tagged with its name (`bootCls`: `SubCover`, `TmpOk`, and `tmpClTouch` from the
  `.touch` files).
- **`S/BootCrashSub.lean`** (pure): `TDesc` (the descendants of a directory) and `tDesc_area_uniq`: in
  a `TreeWf` tree, the subtrees under two entries of a root are disjoint. Also `bootSubs`, `bootOthers`,
  `bootWn`, `bootN`, `bootTaken`/`bootRest` (`bootTaken_nodup`, `dom_perm_taken`), `BootFo`, `bootCls`,
  `bootCls_subCover`, `bootCls_tmpOk`, and `List.Nodup.mapOnW`.
- **`S/BootCrashRes.lean`**: `osNames_split_only` splits a claim `.except X` into `.except (X ++ l)`
  and one `.only [b]` per name of `l`. `bigSepM_sub_list` and `bigSepM_names` pick map entries out of
  a list. `walDirFiles`, `tmpDirFiles` and `walDir_boot` handle one directory each.

## Statement changes

- **`walInv_crash`** (`S/Crash.lean`, internal, no importer outside the WAL), per the coordinator's note
  (`notes/wal-units/durable.md`, recommendation (a')):
  - It takes `crashRest … D` with `hD : ∀ i ∈ D, ¬ InAreaDir V'.now jr i`, where `InAreaDir m jr i`
    says the file is named in a directory that an entry of `jr` names.
  - It takes only the old segments named in such a directory, plus the boot files.
  - It still learns the crash of every old segment (`SegCrashAt`), so `walCrash_pure` is unchanged.
  - It returns `crashRest … (D' ++ D)` with `∀ i ∈ D', InAreaDir V'.now jr i`, and also exports
    `TreeWf R V'.now`. `walStart` is unchanged.
  - It now works in either order with durable's lemma:
    - **WAL first**: durable's `hD` follows from `InAreaDir` through `durCrash_hD`. A file's unique
      location is in a directory named by an entry, and the oracle's directory `jo` is a root, which no
      entry names (`TreeWf`).
    - **Durable first** (`durInv_crash0`): durable's location fact gives this `hD` the same way.
- Supporting changes, all statements of my own lemmas:
  - `crashRestAt_takeIf` (`GooseLang/Ext/Fs/CrashTakeFiles.lean`, new): with `tk = false` it learns
    `FileCrashAt` without taking the file. `crashRestAt_take` is now its corollary, with its statement
    unchanged.
  - `crashRestAt_take_tok`, `crashRestAt_take_seg` and `crashRest(At)_take_segs` (`S/CrashTakeSeg.lean`)
    take a selector `tk`. Only the start of a selected file is transferred, and only a selected file
    needs to be outside `D`.

## Hypotheses / decisions left

- **`BootFo` is still a premise.** It says every WAL directory and every `nm.tmp` directory of the area
  holds only files, and that no `nm.tmp` is a file. It is narrower than the ledger's `hfo` (2026-11-14,
  "`hfo` not derivable") and adds the "no `nm.tmp` is a file" part, which `TmpOk` needs. It is true of
  the Go code (the WAL creates nothing else there), but the WAL invariant as it stands cannot derive it.
  It becomes derivable once `walFoRes` lands, which the coordinator adopted (U3 log, third session; 3-5
  sessions, with a cheaper alternative recorded there). Until then the client's crash invariant must
  carry `BootFo` of the crashed tree, which no client can discharge either: it blocks a closed result
  exactly as `hfo` did.
- No user decision reached.

## Next

- U5's `tester_crash`:
  1. `walInv_crash` (with durable's `D`, or `[]`), then durable's `durInv_crash`, with `hD` through
     `durCrash_hD` and `InAreaDir`;
  2. in the new generation, after `wp_osShare`, `walBootCrash` and durable's `durBoot`, each on its own
     claims: the oracle directory's claim is in `bootRest` (`mem_bootRest_root`).
- `walFoRes`, which would discharge `BootFo`.
