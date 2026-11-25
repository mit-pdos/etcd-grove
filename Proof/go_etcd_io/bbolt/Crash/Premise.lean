/- Lean-first (no Rocq counterpart).

# The crash premise of bbolt's crash proof

`BoltCrashWhole`, bbolt's own statement of the crash premise of C-I1's `backend.BoltCrashWhole`
(`Proof/go_etcd_io/etcd/server/v3/storage/backend/CrashInterim.lean`, whose docstring gives the
reasons it is true and its reviews), so that bbolt's crash proof (`Crash/`) states it without
importing the etcd backend.

**Restated 2026-11-25** (the bbolt-crash lead's proposal, to go to the owner): a slot that
validates holds its first 56 meta bytes as of one change `n`, as before, **and each of its 8
checksum bytes as of a change `m ≤ n`**. C-I1's text fixes only the 56 bytes, which lets the
checksum bytes come from a *newer* write than the fields; then an old slot's fields can validate
with a checksum mixed from a later write (a torn slot left by one crash, rewritten by the next
generation's commit, torn again), and `Open` picks a dead commit. What configuration C does
(`notes/axiom-review/fs-v2-r6/e2e/README.md`): a tear inside one write is a *prefix* (new bytes up to
a cut, old after it), or a mix of two consecutive *unsynced* writes of a page; bbolt syncs after each
meta write, so only the first kind reaches a meta slot, and a byte at a higher offset is as of the
same change as one at a lower offset or an older one. The 64-byte form ("all 64 bytes as of one
change") would be false on C: a prefix cut inside the checksum and a one-byte coincidence validate a
slot whose bytes are of two changes. This form is implied by the 64-byte one. Satisfiable from every
reachable state with a crash (`boltCrashWhole_exists`: every byte its candidate of stamp 0).

**Trusted** (a premise on the run's crash relation).
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
