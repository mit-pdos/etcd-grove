# Review of `notes/bbolt-port-plan.md` (branch `bbolt-port-plan`, `fba4d70b`), 2026-11-11

The plan ports the real bbolt proof (`origin/lean` `a259c0ef`) from the v1 file extension (`OsFs`) to the
per-byte one (`Fs`, `origin/fs-bytes` `9ef5b9bb`). Part 1 reviews it. Part 2 measures decision (1) on
configuration C (`../fs-config/`).

Files here:

- `inventory.py ROOT` re-derives §1's classification, and `mechanical.py ROOT` checks the "mechanical"
  class. ROOT is `git archive origin/lean Proof/go_etcd_io/bbolt Spec/go_etcd_io/bbolt | tar -x -C ROOT`.
- `pw/` (Go 1.27.3, x/sys v0.48.0) is the pwrite experiment. `run.sh WORKDIR [CASE...]` runs each case on
  a fresh C filesystem (`c_mkfs`, `c_mount`, `c_check`), as a non-root user.
- `results.txt` holds the run's output. `summarize.sh` tabulates it.
- `fetch.sh DIR` fetches the v7.0 kernel files cited below.

## Summary

| # | severity | finding | fix |
|---|---|---|---|
| 1 | **high** (decision 1) | The rule's half "a pwrite that returns an errno landed nothing" is **not needed by bbolt**. v1's `Tx.writeMeta` proof already handles a meta page that fully landed while `WriteAt` returned an error (`Proof/go_etcd_io/bbolt/Tx__writeMeta.lean:96`: `(j = 0 ∨ j = 4096) ∧ (err = nil → j = 4096)`; v1's D22 allowed `j = len` with `err ≠ nil`). This is also the half that has kernel exceptions (below). | Make the trusted rule the weaker one: **the landed prefix is empty, whole, or ends on a 4096-byte file-page boundary, whatever the errno** (`k = 0 ∨ k = len ∨ (off + k) % 4096 = 0`, and `e = 0 → 0 < k`). It gives D22 as a consequence, it is all bbolt uses, and it survives every kernel path found. |
| 2 | medium (decision 1, text) | The claim "Go's `WriteAt` loop returns either the whole page or nothing, with the page cache untouched on error" holds only for a one-page aligned write. For a multi-page write, `os.File.WriteAt` returns `(0, err)` after it landed a page-cut prefix, because the retry of a short count fails and `n += m` is skipped on error (`os/file.go:251-260`). This was measured 19 times under ENOSPC and twice under EFBIG. The fs-bytes model already returns `0` on error. | Correct the text. The `WriteAt` spec's error case must keep `j` as any page cut (not 0) for data-page runs and `DB.init`'s 4 pages. Side finding: this behaviour contradicts `io.WriterAt`'s "returns the number of bytes written", a Go stdlib defect not recorded anywhere. |
| 3 | medium (decision 2) | The plan rejects "carry the bytes" because "the writer owns them". That reason is wrong. `Covers` is over the interval `[dlo, dhi)`, and the interval spans committed pages held by the store between dirty pages. Under `NoSync` no sync runs, so the interval grows across transactions. The byte-less spec is therefore forced, not just convenient. Separately, "`m'` = `m` but the size bounds and the durable range unchanged" ignores what a sync changes past the size. `OsFile.synced` resets every byte's candidates, past the size included (`diskByte`: the page-cache value in the last page, 0 beyond), and `OsMeta.synced` sets `tc := ∅` and `zf := some (pageUp size)`. A resource that keeps an old `tc`/`zf` must still predict a superset of the state's candidates, because later grows and extends build new bytes' candidates from the resource's `m` (`ofResize`, `ofWrite`'s gap). | Keep decision (2), with a stated reason. Define the relaxation field by field (byte candidates ⊇; `[dlo, dhi)`, `[lo, hi)` wider; `tc`/`zf` give candidate lists that contain the state's). Have the byte-less spec return `{m with tc := ∅}` unless the proof shows the old `tc` stays sound. Check this against minibolt's and walfs's crash proofs before step 3. |
| 4 | medium (inventory) | The inventory undercounts. There are **62** files (20.5k lines) that name a file resource (`osMeta`, `osBytes`, `osSlot`, `osFd`, `OsMeta`, `pwBytes`, `pwSize`, ...), not 52. See the details below. | Fix the counts and lists. Add a manual list for the `(p : GoString)`/`K.p` edits. |
| 5 | medium (API, §3) | `DB.Close.spec` on lean returns `True`: it gives nothing back. Only `DB.Close_kv` returns `fileHolds path D`, and it, like `Open_kv`, is over etcd backend's own axiomatic vocabulary (`backend.fileHolds`, `dbFile`, `Proof/.../storage/backend/InvBbolt.lean:113`), with no OS resource. `isBolt` already hides the path (`Inv/Bolt.lean:116`: `∃ p`). | Drop §3's `DB.Close` change and open question 3 (`γ.ino`). Leave every `_kv` spec unchanged. "Restated the same way" would break about 25 etcd server files that use the path-keyed `backend.fileHolds` (snapshots, `Rename`, `Cleanup`). |
| 6 | low (§3 `Open`) | The post `V' = V ∨ ∃ e, V' = V.push e` says nothing of `path`. A reopen (after `Close` returns `fileHolds`, if it ever does) cannot find the file. | If kept: add `lookupH R V' path = some (.file i)` on success. Today only `Results` uses `Open.spec`, so this can wait. For open question 2: bbolt always passes `O_CREATE` (`db.go:229`), but the existing-file `os.OpenFile.spec` takes any tree fraction, so a fraction variant is cheap. |
| 7 | low (§2.6) | fs-bytes's `File.WriteAt.impl` already chunks at `0x40000000` (`TrustedCode/os.lean` on fs-bytes, the `max` in the `pwrite` loop). Only the spec's `data.length ≤ 2^30` premise needs lifting, with no trusted-model merge for it. The generalization is needed: bbolt writes up to `maxAllocSize - 1` (2 GiB - 1) per `WriteAt` (`tx.go`'s write loop). | Reword §2.6 and step 2. |
| 8 | low (decision 3) | (i) is fine. Note that (ii)'s cost is lower than stated, because etcd's backend uses the `_kv` axioms, not `Open.spec`. Under the weaker rule the gap case behaves like any other: measured, an ENOSPC write past EOF lands nothing (size unchanged) or a page cut with the gap zeroed. | None needed. Keep (i). |
| 9 | info | `os.File.ReadAt` (needs `off + len ≤ size`), `Stat`, `Flock`, `Mmap` (read-only, `MAP_SHARED`), and mapped reads after `pwrite` all port: `osCell_agree` keeps its shape (`GooseLang/Ext/Fs/Specs.lean:1160` against v1's `Specs.lean:1685`), so `cellsR_agree_bytes` ports. `fmtErrorOkOrNil` and `IsPointerError` are missing from every fs-bytes os post, as the plan says. 35+ bbolt files depend on them. | Leave them as planned (merge step 2). |
| 10 | info | A process killed mid-write (`fatal_signal_pending`, `filemap.c:4319`, after a short copy) leaves a mid-page prefix in the page cache. It is never returned, so it is invisible in-process, but a restarted process sees it. | Never apply the rule to a change in flight at a restart or crash (it is a `PWriteFinish` rule only). |

**Details for row 4 (inventory).**

- 10 resource files are missing from the 52:
  - `Commit/PubOk` and `Commit/PwMeta` (`pwBytes`/`pwSize`, the D22 lemma).
  - `Commit/TailFPure`, `Commit/TailFWrap`, `Commit/TailPartErr`, `Commit/TailPub`.
  - `Commit/WriteDefs` (`osSlot`).
  - `Mmap/GrowPure`, `Open/CoreFacts`, `Open/Facts`.
- `Inv/Ctx` is classed as mechanical, but it defines `BC.p : GoString`, the plan's `K.p` → `K.i`.
- Of the 363 variable-only files:
  - 21 use `K.p` (`DB__beginRWTx` 16×, `Commit/Step` 11×, ...).
  - 16 have `(p : GoString)` file binders (`Inv/Bolt` 7×, `Inv/Tx`, `Inv/Txs`, `Commit/TailSlots`, `Write/Retarget`, ...).

  The `sed` does none of these.
- `DB__grow.lean:282` builds a v1 `OsMeta` literal positionally with the fields `named`, `ok`, `dur` and `durHi`, which are gone.
- The totals are 1044 `.lean` files (plan: 812), of which 463 touch the OS layer (plan: 451).

## Part 1 notes

**Spec mapping.**
- `WriteAt` (whole meta, `off ≤ size`, `PwOut`) suffices for every user once rows 1, 7 and 8 are done.
- `Truncate`'s failure case is now "maybe resized" (`ftUndone`). `DB.grow`'s error path must allow either size. `fileOK`'s `hwm·4096 ≤ size` stays true, since the file only grows.
- `Fdatasync`/`File.Sync`: `DB.grow` calls `File.Sync` too, so the byte-less spec is needed for both.
- `OpenFile` fixes the flag to `0x42`. That is fine as long as `OptsM.ok` excludes `ReadOnly` and custom `OpenFile`, as on lean.
- `PageSize` must stay 4096 in `OptsM.ok` (it does, `Api.lean:43`, `:148`). Otherwise the meta page is several OS pages and D22's consequence fails under either rule.

**Invariants.** The renamed `fileHoldsDef` and `osSlot` carry what the v1 proof uses: values only, and the store owns its slots whole (`Inv/Store.lean:60`, `:167`).

**Order and merge.** Step 1 should be the weaker rule (row 1). Step 3's relaxation is the step most likely to fail: prove the `tc`/`zf` part first (row 3).

## Part 2: decision (1) measured on C

`run.sh` ran each case on a fresh C filesystem; `check.sh` passed for every one, with mount options `noquota`, `errors=continue`, `data=ordered`, `delalloc` and `dioread_nolock`. Each case writes a non-zero pattern, then `pread`s the range back to see what the page cache holds. Two modes:
- **sys**: one `unix.Pwrite`.
- **go**: `os.File.WriteAt`.

`summarize.sh` gives this table:

| case (C unless marked) | sys | go |
|---|---|---|
| ENOSPC: nearly full fs, swept over 0–3071 free blocks; aligned 16 pages; offsets 100 and 4000 with 16 pages + 300; 8 MiB at 100; a write past EOF (gap); one aligned page; one page at 3000 | 18× `ENOSPC` with **nothing landed** (size unchanged). 17× short count, **all ending at a page boundary** of the file offset (8192, 16384, 32768, 131072, ..., 6291456: folio boundaries), landed = count, **0 bytes beyond**, size = off + n. The rest were full writes. | 18× `(0, ENOSPC)`, nothing landed. 17× **`(0, ENOSPC)` with a page-cut prefix landed**. |
| EFBIG: writes ending past `s_maxbytes` = 2^44 - 4096 (measured), and writes at or past it | 2× short count ending at `s_maxbytes` (page aligned). 2× `EFBIG` with nothing landed. | 2× `(0, EFBIG)` after 100 and 5000 bytes landed. |
| signals: 3 × 256 MiB writes at off 100 while 155,816 `SIGUSR1` arrive; untouched anonymous-mmap source pages | always full | always full |
| contrast, not C: `RLIMIT_FSIZE` = 10000, write at 8000 | short count 2000, ending at 10000: **mid-page** | `(0, EFBIG)`, 2000 landed |
| contrast, not Go memory: source page PROT_NONE, off 100 | short count 8192, ending at 8292: **mid-page** (`EFAULT` after progress) | `(0, EFAULT)`, 8192 landed |
| contrast, not C: `FS_IOC_SHUTDOWN` during a 512 MiB write | short count 222,298,012 (a page boundary), landed = count (read through a mapping) | — |

Two things in the ENOSPC rows:
- The aligned 16-page and one-page writes landed all or nothing at every free-block count: ext4 used one large folio, reserved as a unit.
- An ENOSPC write past EOF left the size unchanged, gap included.

**Mechanism (v7.0).**
- `generic_perform_write` (`mm/filemap.c:4296-4386`) advances `written` only by `write_end`'s status for a folio, and returns `written ? written : status`.
- A `write_begin` failure (ENOSPC/EDQUOT from `ext4_da_reserve_space`/`dquot_reserve_block`, `fs/ext4/inode.c:1625`; ENOSPC in `ext4_write_begin`'s allocation, the non-delalloc path `ext4_nonda_switch` takes near full, `:3081`, `:1283`; EIO from `ext4_emergency_state`) stops the loop before any copy into that folio. So a short count ends on a folio boundary, and folios are page-aligned.
- `generic_write_check_limits` (`fs/read_write.c:1711`) cuts at `s_maxbytes` (`ext4_max_size`, `fs/ext4/super.c:3432`: `(2^32-1) << 12`) or at `RLIMIT_FSIZE`. Only the latter can end mid-page, and it is unlimited on C.
- A cut inside a folio needs a short copy (a not-present source page) that `block_write_end` commits on an uptodate folio (`fs/buffer.c:2265`), followed by a stop before the folio is finished. The possible stops:
  - `EFAULT` from `fault_in_iov_iter_readable` (unreadable source; never live Go memory).
  - A fatal signal (the process dies).
  - A `write_begin` failure on the same folio. Its blocks are already reserved, so this needs a journal abort or an allocation failure in jbd2.

  Non-fatal signals never interrupt (only `fatal_signal_pending` is checked), as measured.

**The half "errno ⇒ nothing landed": true on C, with exceptions in the source.**
- `ext4_da_do_write_end` (`inode.c:3202-3270`) commits the copy and `i_size`, then returns `PTR_ERR(handle)` (`:3263`) if `ext4_journal_start` fails.
- `ext4_write_end` (`:1437-1504`) returns `ret ? ret : copied`, where `ret` comes from `ext4_mark_inode_dirty` or `ext4_journal_stop`.

Both happen only on an extending write (`disksize_changed`, or `pos > old_size`: the NoGrowSync gap case). If that folio is the first, the call returns an errno with bytes landed. Otherwise it returns `written` while the folio beyond it landed. Under `O_DSYNC`, `generic_write_sync` (`ext4_buffered_write_iter`, `fs/ext4/file.c:286-307`) returns the sync's error after landing bytes; bbolt and the model's `0x42` flag never set it. None of this is reachable on C without a journal abort (media error), or an allocation failure that C's statement does not exclude explicitly. The weaker rule of row 1 holds even on these paths, because what lands is a whole folio, which is a page cut.

**Verdict on decision (1).**
- "Errno lands nothing": measured true on C (20/20 syscall errors landed nothing, ENOSPC and EFBIG). The kernel's guarantee rests on `write_end` never failing after committing, which ext4 does not guarantee (journal start or inode dirtying on an extending write). It is unnecessary for bbolt, so drop it.
- "A short count ends on a page boundary": measured true on C (19/19 short counts, ENOSPC and `s_maxbytes`, landed exactly the count with nothing beyond). From the source, it is true for readable sources and `RLIMIT_FSIZE` unlimited. Both contrasts (`RLIMIT_FSIZE`, `EFAULT`) produced mid-page counts, so both are load-bearing parts of C and of "Go memory" in the rule's docstring.
