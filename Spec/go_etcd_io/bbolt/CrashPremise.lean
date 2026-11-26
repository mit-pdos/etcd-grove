/- Lean-first (no Rocq counterpart).

# bbolt's crash premise: a meta page that validates after a crash is not torn

**Trusted** (a premise on the run's crash relation: C-I1's `dbCrash` takes it as `hQ`; bbolt's crash
proof, `Proof/go_etcd_io/bbolt/Crash/`, rests on it). One definition: C-I1's `backend.BoltCrashWhole`
abbreviates this one.

**The statement.** For the files of `I` (the database's inode) whose size has not changed since their
last sync and which have no change in flight past their end, at a crash: if meta page `j < 2` of the
crash image validates (`boltMetaValidates`: bbolt's `Meta.Validate`, magic, version and the FNV-64a of
the first 56 meta bytes in bytes 56 to 64), its first 56 meta bytes are the slot as of one change `n`
(`valAt`), and each of its 8 checksum bytes as of a change `m ≤ n`.

**Why it is true of configuration C** (Linux 7.0, ext4 defaults, `notes/axiom-review/fs-config/`).
- How a page tears on C (`notes/axiom-review/fs-v2-r6/e2e/README.md`, script `e2e.sh`/`scan.py`, every
  write of a dm-log-writes log a crash point):
  - (A) inside one write, a *prefix*: new bytes up to a cut, old after it. That is the only tear of a
    page with one write in flight: runs `S0`/`S2` (`STABLE=1`, the device waits for writeback before a
    page is rewritten) checked 4,735,235 crash points, of which 7 left a torn page, each a new-prefix cut;
  - (B) a mix of two consecutive *unsynced* writes of a page, at any byte (`STABLE=0` runs `B1`/`C1`/`C2`:
    old-prefix and multi-run images). This needs a page rewritten while its previous write is under
    writeback.
- bbolt `fdatasync`s after each meta write before the slot is written again (`Tx.Commit`, `init`;
  the next write of a slot is two commits later), so (B) never reaches a meta slot of a database opened
  syncing, and after a reboot the slot's durable bytes are not under writeback. (A database opened with
  `NoSync`, defrag's temporary one, can reach (B); the premise holds there up to an FNV-64a collision.)
  Tears are not confined to a source page boundary: on C one `pwrite` can be cut at an arbitrary byte, from
  a page-aligned source buffer too (a source page moved during the copy, e.g. by `MADV_COLLAPSE`: measured in
  the page cache, unmeasured on disk; `notes/axiom-review/cstar-independent.md`). A cut inside the 56 field bytes
  mixes two writes' fields, and the premise excludes such a slot if it validates:
  - over a valid older meta, that needs an FNV-64a prefix collision between bbolt-written bytes;
  - over the torn residue of an earlier crash, which bbolt keeps across a reopen, it can rebuild an older
    meta byte for byte with no collision (`notes/axiom-review/t1b-options.md`). That is harmless to bbolt (the
    rebuilt meta's txid is the older one), but it is outside the premise.

  Justifying the exclusion up to an accidental FNV-64a coincidence needs torn residue not to survive a
  reopen: an open decision (option C★: `Open` poisons an invalid slot), pending.
- So in a crash image of a meta slot, a byte at a higher offset is as of the same change as one at a
  lower offset, or an older one: the 56 field bytes as of `n` (for a validating slot, by FNV-64a the
  fields and the checksum cannot come from two different metas but by a 2^-64 collision, the
  probabilistic part) and the checksum bytes, at higher offsets, as of `m ≤ n`.

**Why not weaker or stronger.**
- The 56-byte form (C-I1 until 2026-11-25) admits, in the model's per-byte crash, a double-crash image
  that revives a dead commit, so `dbCrash` was false of the model:
  - a crash tears commit `t+1`'s meta (its new fields, a checksum partly old: invalid);
  - the next generation opens at `t` and commits `t+1` again into that slot, reusing the dead commit's
    pages;
  - a second crash keeps the old fields with checksum bytes from the new write that complete the old
    checksum (one coinciding byte per torn checksum byte);
  - `Open` picks the dead `t+1`, whose pages are overwritten.
  That image takes the checksum bytes from a *newer* write than the fields, which (A) cannot produce.
- The 64-byte form ("all 64 bytes as of one change") is equivalent to this one for the metas bbolt
  writes (a checksum byte that coincides with the newer meta's equals it by value) and differs only for
  files whose bytes bbolt did not write; this form is implied by it, and asks less of such files.

Satisfiable from every reachable state with a crash (`boltCrashWhole_exists`: every byte its candidate
of stamp 0). Reviews: `notes/axiom-review/c-i1-bbolt-crash.md`, `c-i1-takeput.md`,
`c-i1-monotone.md`.
-/
module

public import GooseLang.Ext.Fs.Impl
public import Spec.hash.fnv.Model
public import GooseLang.Ext.Fs.Tests

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

/-- A little-endian number (C-I1's `backend.leNat`). -/
def leNat (l : List w8) : Nat := l.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- What bbolt's `Meta.Validate` checks of the 64 bytes `r` of a meta (the page's bytes 16 to 80,
after its header): the magic `0xED0CDAED`, the version `2`, and the checksum (bytes 56 to 64) the
FNV-64a of the first 56 (C-I1's `backend.boltMetaValidates`; `Crash/Meta.lean` proves it is
`metaValid` of the decoded meta). -/
def boltMetaValidates (r : List w8) : Prop :=
  leNat (r.take 4) = 0xED0CDAED ∧ leNat ((r.drop 4).take 4) = 2 ∧
    leNat (r.drop 56) = (hash.fnv.fnv64a (r.take 56)).toNat

/-- **The crash premise: a meta page that validates after a crash is not torn** (see the file
header). For each file `i` of `I` whose size has not changed since its last successful sync and which
has no change in flight past its end, at a crash from `st` to `st'`: if meta page `j < 2` of the
crash image validates, its first 56 meta bytes are the slot as of one change `n` (`valAt`), and each
of its checksum bytes (meta bytes 56 to 64) as of a change `m ≤ n`. -/
def BoltCrashWhole (I : Fs.Ino → Prop) (st st' : Fs.OsState) : Prop :=
  ∀ (i : Fs.Ino) (f f' : Fs.OsFile), I i → st.fs.files !! i = some f → st'.fs.files !! i = some f' →
    f.sizeLo = f.size → f.sizeHi = f.size →
    (∀ t c, st.proc.inflight !! t = some c → c.ino = i → c.target ≤ f.size) →
    ∀ j < 2, 4096 * j < f'.size →
      boltMetaValidates ((List.range 64).map fun k => f'.cache (4096 * j + 16 + k)) →
      ∃ n, (∀ k < 56, f'.cache (4096 * j + 16 + k) = Fs.valAt (f.cand (4096 * j + 16 + k)) n) ∧
        ∀ k, 56 ≤ k → k < 64 →
          ∃ m ≤ n, f'.cache (4096 * j + 16 + k) = Fs.valAt (f.cand (4096 * j + 16 + k)) m

/-- **`BoltCrashWhole` is never vacuous at a crash**: from every reachable state (`CacheOk`) with a
machine crash, the crash that leaves every named file as of its last sync (`Tests.durCrash`) is a
crash satisfying it (every byte its candidate of stamp 0). -/
theorem boltCrashWhole_exists (I : Fs.Ino → Prop) {st st' : Fs.OsState} (hok : Fs.Tests.CacheOk st)
    (hc : Fs.MachineCrash st st') : ∃ st'', Fs.OsCrash st st'' ∧ BoltCrashWhole I st st'' := by
  refine ⟨Fs.Tests.durCrash st st', Fs.Tests.durCrash_machine hok hc, ?_⟩
  intro i f f' _ hf hf' _ _ _ j _ hsz _
  have key : ∀ k < 64, f'.cache (4096 * j + 16 + k) = Fs.valAt (f.cand (4096 * j + 16 + k)) 0 := by
    intro k _
    rw [Fs.Tests.durCrash_files, hf] at hf'
    split at hf'
    · simp only [Option.map_some, Option.some.injEq] at hf'
      subst hf'
      simp only [Fs.Tests.durFile, Fs.OsFile.ofDisk] at hsz ⊢
      rw [Fs.diskByte, if_pos]
      simp only [Fs.pageIn, decide_eq_true_eq]
      omega
    · cases hf'
  exact ⟨0, fun k hk => key k (by omega), fun k _ hk => ⟨0, Nat.le_refl 0, key k hk⟩⟩

end bbolt
end EtcdGrove
end Perennial
