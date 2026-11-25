/- Lean-first (no Rocq counterpart).

# The crash premise of bbolt's crash proof

`BoltCrashWhole` restated in bbolt's namespace, word for word the definition of C-I1's
`backend.BoltCrashWhole` (`Proof/go_etcd_io/etcd/server/v3/storage/backend/CrashInterim.lean`, whose
docstring gives the reasons it is true and its reviews), so that bbolt's crash proof (`Crash/`) states
it without importing the etcd backend. C-I1's becomes an abbreviation of this one.

**Trusted** (a premise on the run's crash relation, as C-I1's: the same text).
-/
module

public import GooseLang.Ext.Fs.Impl
public import Spec.hash.fnv.Model

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

/-- **The crash premise: a meta page that validates after a crash is not torn** (C-I1's
`backend.BoltCrashWhole`, the same definition; see its docstring). For each file `i` of `I` whose
size has not changed since its last successful sync and which has no change in flight past its end,
at a crash from `st` to `st'`: if meta page `j < 2` of the crash image validates, its first 56 meta
bytes are the slot as of one change `n` (`valAt`). -/
def BoltCrashWhole (I : Fs.Ino → Prop) (st st' : Fs.OsState) : Prop :=
  ∀ (i : Fs.Ino) (f f' : Fs.OsFile), I i → st.fs.files !! i = some f → st'.fs.files !! i = some f' →
    f.sizeLo = f.size → f.sizeHi = f.size →
    (∀ t c, st.proc.inflight !! t = some c → c.ino = i → c.target ≤ f.size) →
    ∀ j < 2, 4096 * j < f'.size →
      boltMetaValidates ((List.range 64).map fun k => f'.cache (4096 * j + 16 + k)) →
      ∃ n, ∀ k < 56, f'.cache (4096 * j + 16 + k) = Fs.valAt (f.cand (4096 * j + 16 + k)) n

end bbolt
end EtcdGrove
end Perennial
