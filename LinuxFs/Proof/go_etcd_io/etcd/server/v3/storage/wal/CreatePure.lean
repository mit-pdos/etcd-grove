/- Lean-first (no Rocq counterpart).

# `Create`'s names (W4, eleventh session)

`dir = r/nm` (`InArea`), `nm.tmp` (`tmpName nm`): `filepath.Clean(dir) + ".tmp"` is `r/nm.tmp`; `nm.tmp`
is a name (`NameOk`), no WAL name, no `.wal` name, a slot of the area (`AreaSlot`); a spine is to a
clean absolute path (`osPathS_cleanAbs`, here for any `HasLC`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PipeLemmas
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateArea

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProofMode Fs

theorem dir_child {r dir nm : GoString} (hin : InArea r dir nm) : dir = child r nm := by
  rw [hin.2]; simp [child]; rfl

theorem tmp_path (r nm : GoString) : child r nm ++ go!".tmp" = child r (tmpName nm) := by
  simp [child, tmpName]

theorem clean_child {r nm : GoString} (hr : filepath.CleanAbs r) (hnm : NameOk nm) :
    path.cleanModel (child r nm) = child r nm := by
  have h := filepath.cleanAbs_append r nm hr (cleanSeg_of_nameOk hnm)
  have e : r ++ [path.slash] ++ nm = child r nm := by simp [child]; rfl
  rw [e] at h
  exact filepath.cleanModel_cleanAbs _ h

/-- **`filepath.Dir` of the WAL's directory** (`Create`'s parent fsync): the area. -/
theorem dir_child_model {r nm : GoString} (hr : filepath.CleanAbs r) (hnm : NameOk nm) :
    path.dirModel (child r nm) = r := by
  have h := filepath.dirModel_name r nm hr (cleanSeg_of_nameOk hnm)
  have e : r ++ [path.slash] ++ nm = child r nm := by simp [child]; rfl
  rw [e] at h
  exact h

theorem tmpName_nameOk {nm : GoString} (h : NameOk nm) : NameOk (tmpName nm) := by
  obtain ⟨h1, -, -, h4, h5⟩ := h
  refine ⟨by simp [tmpName], ?_, ?_, ?_, ?_⟩
  · intro e; have := congrArg List.length e; simp [tmpName] at this
  · intro e; have := congrArg List.length e; simp [tmpName] at this
  · simp only [tmpName, List.mem_append, not_or]; exact ⟨h4, by decide⟩
  · simp only [tmpName, List.mem_append, not_or]; exact ⟨h5, by decide⟩

theorem tmpName_not_walName (nm : GoString) : ¬ walNameOk (tmpName nm) := by
  intro hw; apply hw.2.2; simp [tmpName]

theorem tmpName_walNameP (nm : GoString) : walNameP (tmpName nm) = false := by
  unfold walNameP tmpName
  simp only [decide_eq_false_iff_not]
  intro h
  have := List.IsSuffix.reverse h
  rw [List.reverse_append] at this
  have h4 := this.getElem (show 1 < ([46#8, 119#8, 97#8, 108#8] : List w8).reverse.length by decide)
  simp at h4

theorem tmpName_areaSlot {nm : GoString} (h : walNameOk nm) : AreaSlot (tmpName nm) :=
  ⟨nm, h, .inr ⟨go!"tmp", by simp [tmpName]⟩⟩

theorem tmpName_ne (nm : GoString) : tmpName nm ≠ nm := by
  intro e; have := congrArg List.length e; simp [tmpName] at this

theorem areaOk_tmp {N : NameSet} {h : NamesH} {cl : List (GoString × Claim)} {Wn : List GoString}
    {nm : GoString} (hok : AreaOk N h cl Wn) (hnm : walNameOk nm) : N.Mem (tmpName nm) := by
  have := hok.2.1 nm go!"tmp" hnm; simpa [tmpName] using this

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- A path in the shared mode is a clean absolute path. -/
theorem osPathS_cleanAbs' (R : Roots) (d : GoString) (dq : DFrac) (j : Ino) :
    osPathS (GF := GF) R d dq j ⊢ ⌜filepath.CleanAbs d⌝ := by
  unfold osPathS
  iintro ⟨%r, %j0, %cs, %h, -⟩
  obtain ⟨hR, hr, hcs, rfl⟩ := h
  ipureintro; exact cleanAbs_joinPath hR hr hcs

end iris

end WalFs
end EtcdGrove
end Perennial

end
