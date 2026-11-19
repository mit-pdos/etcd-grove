/-
The lemmas of `selectWALFiles.lean`'s proof (`walNamesOut_str`, `walSearchFrom_le`, ...), in a module of
their own so that `openAtIndex`'s lemmas import them without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__GetIndex
public import Spec.fmt.ErrorfErrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs

/-- The names `readWALNames` returns from a directory `selectWALFiles` can read are segment names. -/
theorem walNamesOut_str {N : NameSet} {h : NamesH} {ws : List GoString} (hd : WalDirNamesOk N h)
    (ho : WalNamesOut N h ws) : ∀ n ∈ ws, ∃ s i, n = fmt.walNameStr s i := by
  intro n hn
  have hm := (ho.2.2.1 n hn).2
  obtain ⟨hN, hs⟩ := hd n hm.1
  exact hs (ho.2.2.2.1 n hN hn)

/-- `walSearchFrom` finds a position below its bound. -/
theorem walSearchFrom_lt {idxs : List w64} {index : w64} :
    ∀ {n k : Nat}, walSearchFrom idxs index n = some k → k < n
  | 0, _, h => by simp [walSearchFrom] at h
  | n + 1, k, h => by
    unfold walSearchFrom at h
    split at h
    · cases h; omega
    · exact Nat.lt_succ_of_lt (walSearchFrom_lt h)

/-- `walSearchFrom` finds a position whose index is at most `index`. -/
theorem walSearchFrom_le {idxs : List w64} {index : w64} :
    ∀ {n k : Nat}, walSearchFrom idxs index n = some k → uint.Z (idxs.getD k 0) ≤ uint.Z index
  | 0, _, h => by simp [walSearchFrom] at h
  | n + 1, k, h => by
    unfold walSearchFrom at h
    split at h
    · cases h; assumption
    · exact walSearchFrom_le h

end EtcdGrove
end Perennial
