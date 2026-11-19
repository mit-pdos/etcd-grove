/-
`storage.OpenSnapshotBackend`'s lemma (wal-link, 2026-11-19, option B1): the database snapshot's
file and the backend's file are names of one directory, the snapshot directory `config.snapDirOf dd`
(`os.Rename.spec`'s premise). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs
public import GooseLang.Ext.Fs.TreeLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace snap

/-- A database snapshot's name is a directory entry's name (`NameOk`). -/
theorem snapDBName_nameOk (i : w64) : NameOk (snapDBName i) := by
  have hl : (snapDBName i).length = 24 := by
    simp [snapDBName, WalFs.hex16]
  refine ⟨fun e => by rw [e] at hl; simp at hl, fun e => by rw [e] at hl; simp at hl,
    fun e => by rw [e] at hl; simp at hl, fun hc => ?_, fun hc => ?_⟩
  · unfold snapDBName at hc
    rcases List.mem_append.1 hc with h | h
    · exact WalFs.hex16_ne_slash _ _ h rfl
    · simp at h; rcases h with h | h | h | h | h | h | h | h <;> exact absurd h (by decide)
  · unfold snapDBName at hc
    rcases List.mem_append.1 hc with h | h
    · exact WalFs.hex16_ne_nul _ _ h rfl
    · simp at h; rcases h with h | h | h | h | h | h | h | h <;> exact absurd h (by decide)

/-- **The snapshot's file and the backend's file are in one directory** (`os.Rename.spec`'s
premise): both names of `config.snapDirOf dd`. -/
theorem snapDBPath_parent [GooseExts] (dd : GoString) (i : w64) :
    parentOf (snapDBPath (config.snapDirOf dd) i) = parentOf (config.backendPathOf dd) := by
  have hdb : NameOk go!"db" := by unfold NameOk; decide
  show parentOf (Fs.child (config.snapDirOf dd) (snapDBName i)) =
    parentOf (Fs.child (config.snapDirOf dd) go!"db")
  rw [Fs.parentOf_child' _ _ (snapDBName_nameOk i), Fs.parentOf_child' _ _ hdb]

end snap
end EtcdGrove
end Perennial
