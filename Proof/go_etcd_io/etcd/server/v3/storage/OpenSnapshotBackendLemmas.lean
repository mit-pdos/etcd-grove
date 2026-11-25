/-
`storage.OpenSnapshotBackend`'s lemma (wal-link, 2026-11-19, option B1): the database snapshot's
file and the backend's file are names of one directory, the snapshot directory `config.snapDirOf dd`
(`os.Rename.spec`'s premise); and (wal-fsfix2, 2026-11-20) each snapshot file of a data directory that
fits fits (`pathFits_snapDBPath`); and (pin e94f33b50, 2026-11-25) `filepath.Dir` of the backend's path is
the snapshot directory (`config.dirModel_backendPathOf`: the directory the fork's `syncDir` after the rename
syncs). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs
public import GooseLang.Ext.Fs.TreeLemmas
public import Proof.go_etcd_io.etcd.server.v3.config.PathFits
public import Proof.path.CleanIdem

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

/-- **A snapshot file of a data directory that fits fits** (`bootOk`'s `Hsfree` claims carry it:
implied by `bootCfgFresh`'s `DirFits`, wal-fsfix2). -/
theorem pathFits_snapDBPath {dd : GoString} (hd : Fs.DirFits dd) (i : w64) :
    Fs.PathFits (snapDBPath (config.snapDirOf dd) i) :=
  config.pathFits_snapDir_child hd (by simp [snapDBName, WalFs.hex16])

end snap

namespace path

/-- **`Clean(p + "/") = Clean(p)`** for a non-empty `p`: the loop skips a final `/` (as
`cleanModel_snoc`'s separator step). -/
theorem cleanModel_snoc_slash (p : List w8) (hp : p ≠ []) :
    cleanModel (p ++ [slash]) = cleanModel p := by
  have h0 : 0 < p.length := List.length_pos_iff.2 hp
  have hg : (p ++ [slash]).getD 0 0 = p.getD 0 0 := getD_app_lt h0
  have hne : p ++ [slash] ≠ [] := by simp
  generalize hrt : decide (p.getD 0 0 = slash) = rt
  unfold cleanModel
  rw [if_neg hne, if_neg hp]
  simp only
  rw [hg, hrt, cleanLoop_eq_S, cleanLoop_eq_S]
  have happ := cleanLoopS_app (p := p) (t := [slash]) (Or.inr rfl) rt (if rt then 1 else 0)
    (if rt then [slash] else []) (if rt then 1 else 0) (by split <;> omega)
  rw [happ]
  generalize cleanLoopS p rt (if rt then 1 else 0) (if rt then [slash] else []) (if rt then 1 else 0) = st
  obtain ⟨r1, o, d⟩ := st
  simp only
  have hsl : (p ++ [slash]).getD p.length 0 = slash := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]; simp
  rw [cleanLoopS_step _ _ _ _ _ (by simp), cleanStep_slash _ _ _ _ _ hsl]
  simp only
  rw [cleanLoopS_stop _ _ _ _ _ (by simp)]

end path

namespace config

open path in
/-- **`filepath.Dir` of the backend's path is the snapshot directory** (pin e94f33b50: the
directory `OpenSnapshotBackend`'s `syncDir` syncs after the rename), for any data directory: the
last `/` of `snapDir/db` is the one before `db`, and `Clean(snapDir + "/")` is the snapshot
directory, a `Join`'s output. -/
theorem dirModel_backendPathOf [GooseExts] (dd : GoString) :
    dirModel (backendPathOf dd) = snapDirOf dd := by
  have e : backendPathOf dd = snapDirOf dd ++ [slash] ++ go!"db" := by
    simp [backendPathOf]; rfl
  have hsum : ([dd, go!"member", go!"snap"].map List.length).sum ≠ 0 := by simp
  have hc : cleanModel (snapDirOf dd) = snapDirOf dd := cleanModel_joinModel _ hsum
  have hne : snapDirOf dd ≠ [] := by
    intro h
    have h1 : cleanModel (snapDirOf dd) = go!"." := by rw [h]; unfold cleanModel; simp
    rw [hc, h] at h1
    exact absurd h1 (by decide)
  have hl := lastIndexByte_seg (snapDirOf dd) go!"db" (by decide)
  rw [e]
  unfold dirModel splitModel
  rw [hl]
  have : (((snapDirOf dd).length : Int) + 1).toNat = (snapDirOf dd).length + 1 := by omega
  rw [this]
  have ht : List.take ((snapDirOf dd).length + 1) (snapDirOf dd ++ [slash] ++ go!"db") =
      snapDirOf dd ++ [slash] := by
    rw [List.append_assoc, List.take_append]; simp [List.take_of_length_le]
  simp only [ht]
  rw [cleanModel_snoc_slash _ hne, hc]

end config
end EtcdGrove
end Perennial
