/-
**The snapshot directory's paths fit** (wal-fsfix2, 2026-11-20, approved by the user): with
`config.snapDirOf` Go's `filepath.Join(d, "member", "snap")` (`config/Defs.lean`), a data directory
that fits (`Fs.DirFits`: under 3800 bytes, no component over 255 bytes; `bootCfgFresh`'s) gives a
snapshot directory at most 12 bytes longer with the window property (`Clean` of a non-empty path
lengthens nothing and makes no longer component: `Proof/path/CleanFits.lean`), so every name of at most 255 bytes in it fits
(`Fs.PathFits`): the backend's file (`backendPathOf`) and each snapshot file (`snap.snapDBPath`,
`OpenSnapshotBackendLemmas`). These are the `PathFits` conjuncts of `bootOk`'s claims (`Hpath`,
`Hsfree`): no longer asserted by the bootstrap contract beyond its precondition. And of a clean
absolute data directory the snapshot directory is `d/member/snap`, under `d`. Untrusted.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.config.Defs
public import Proof.path.CleanFits
public import Proof.path.filepath.Names

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace config

open path

/-- `Join(d, "member", "snap")`'s buffer: `d/member/snap`, or `member/snap` for an empty `d`. -/
theorem joinBuf_snapDir (d : GoString) :
    joinBuf [d, go!"member", go!"snap"] [] =
      if d = [] then go!"member" ++ [slash] ++ go!"snap"
      else d ++ [slash] ++ go!"member" ++ [slash] ++ go!"snap" := by
  by_cases hd : d = []
  · subst hd; simp [joinBuf]
  · have h0 : 0 < d.length := List.length_pos_iff.2 hd
    simp [joinBuf, hd, h0]

/-- **The snapshot directory of a data directory that fits**: the window property, and at most 12
bytes longer. -/
theorem snapDirOf_fits {d : GoString} (hd : Fs.DirFits d) :
    Fs.WinOk (snapDirOf d) ∧ (snapDirOf d).length ≤ d.length + 12 := by
  have hsum : ([d, go!"member", go!"snap"].map List.length).sum ≠ 0 := by simp
  unfold snapDirOf joinModel
  rw [if_neg hsum, joinBuf_snapDir]
  split
  · have hne : (go!"member" ++ [slash] ++ go!"snap" : GoString) ≠ [] := by decide
    have hlt : (go!"member" ++ [slash] ++ go!"snap" : GoString).length = 11 := by decide
    obtain ⟨h1, h2⟩ := cleanModel_fits _ hne (Fs.winOk_short (by omega))
    exact ⟨h1, by omega⟩
  · have hw : Fs.WinOk (d ++ [slash] ++ go!"member" ++ [slash] ++ go!"snap") := by
      have h1 := Fs.winOk_child (b := go!"member") hd.2 (by decide)
      have h2 := Fs.winOk_child (b := go!"snap") h1 (by decide)
      simpa [Fs.child, slashB] using h2
    have hne : d ++ [slash] ++ go!"member" ++ [slash] ++ go!"snap" ≠ [] := by simp
    obtain ⟨h1, h2⟩ := cleanModel_fits _ hne hw
    have : (go!"member" : GoString).length = 6 := by decide
    have : (go!"snap" : GoString).length = 4 := by decide
    simp only [List.length_append, List.length_singleton] at h2
    exact ⟨h1, by omega⟩

/-- **A name of at most 255 bytes in the snapshot directory of a data directory that fits fits.** -/
theorem pathFits_snapDir_child {d b : GoString} (hd : Fs.DirFits d) (hb : b.length ≤ 255) :
    Fs.PathFits (Fs.child (snapDirOf d) b) := by
  obtain ⟨hw, hl⟩ := snapDirOf_fits hd
  exact Fs.pathFits_child hw hb (by have := hd.1; omega)

/-- **The backend's file of a data directory that fits fits.** -/
theorem pathFits_backendPathOf [GooseExts] {d : GoString} (hd : Fs.DirFits d) :
    Fs.PathFits (backendPathOf d) :=
  pathFits_snapDir_child hd (b := go!"db") (by decide)

/-- **The snapshot directory of a clean absolute data directory** is `d/member/snap`. -/
theorem snapDirOf_cleanAbs {d : GoString} (hd : filepath.CleanAbs d) :
    snapDirOf d = Fs.child (Fs.child d go!"member") go!"snap" := by
  obtain ⟨segs, hne, hp, rfl⟩ := hd
  have hm : cleanSeg go!"member" := by unfold cleanSeg; decide
  have hs : cleanSeg go!"snap" := by unfold cleanSeg; decide
  have hl := segsPath_length_two segs hne hp
  have h0 : segsPath segs ≠ [] := by intro h; rw [h] at hl; simp at hl
  have hsum : ([segsPath segs, go!"member", go!"snap"].map List.length).sum ≠ 0 := by simp
  have hc := cleanModel_segs (segs ++ [go!"member", go!"snap"]) [] (by simp) (by
    intro x hx; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | rfl | rfl
    · exact hp x hx
    · exact hm
    · exact hs) (Or.inl rfl)
  have he : segsPath (segs ++ [go!"member", go!"snap"]) =
      segsPath segs ++ [slash] ++ go!"member" ++ [slash] ++ go!"snap" := by
    rw [show segs ++ [go!"member", go!"snap"] = (segs ++ [go!"member"]) ++ [go!"snap"] by simp,
      segsPath_snoc, segsPath_snoc]
  unfold snapDirOf joinModel
  rw [if_neg hsum, joinBuf_snapDir, if_neg h0]
  simp only [List.append_nil] at hc
  rw [← he, hc, he]
  simp [Fs.child, slashB]

/-- **The snapshot directory of a clean absolute data directory is under it.** -/
theorem snapDirOf_under {d : GoString} (hd : filepath.CleanAbs d) : IsUnder d (snapDirOf d) := by
  rw [snapDirOf_cleanAbs hd]
  right
  exact ⟨go!"member" ++ slashB :: go!"snap", by simp [Fs.child]⟩

end config
end EtcdGrove
end Perennial
