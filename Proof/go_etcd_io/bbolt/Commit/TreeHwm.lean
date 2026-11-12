/-
**`treeOK` across `Commit`'s steps after the spill** (U10b; batch 39's need 4, pure): spill's
`treeOK (spillC X' C.pages)` is at the high-water mark after the spill; `commitFreelist`'s
`allocate` may raise it before the publish, and the published state `C.publish buf m pages`
differs from `spillC` in its metas and freelist page only. `treeOK` reads the pages, the root, the
mark (monotonically) and the txid; `treeData` the pages and the root.
-/
module

public import Proof.go_etcd_io.bbolt.Model.TreeData

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace bbolt


section tree
variable [GooseExts]

theorem branchWF_mono {pg : List w8} {len h h' : Nat} (hh : h ≤ h') (H : branchWF pg len h) :
    branchWF pg len h' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  exact ⟨h1, h2, h3, fun i hi => ⟨(h4 i hi).1, (h4 i hi).2.1, by have := (h4 i hi).2.2; omega⟩, h5⟩

mutual
theorem treeWF_mono {P : Pages} {h h' : Nat} (hh : h ≤ h') {r : Nat} :
    treeWF P h r → treeWF P h' r
  | .page root pg h1 h2 h3 h4 h5 h6 => .page root pg h1 (by omega) h3 h4 h5 (pageTreeWF_mono hh h6)

theorem pageTreeWF_mono {P : Pages} {h h' : Nat} (hh : h ≤ h') {pg : List w8} {len : Nat} :
    pageTreeWF P h pg len → pageTreeWF P h' pg len
  | .leaf pg len h1 h2 h3 => .leaf pg len h1 h2 fun i hi hb => bucketWF_mono hh (h3 i hi hb)
  | .branch pg len h1 h2 h3 =>
      .branch pg len h1 (branchWF_mono hh h2) fun i hi => treeWF_mono hh (h3 i hi)

theorem bucketWF_mono {P : Pages} {h h' : Nat} (hh : h ≤ h') {v : List w8} :
    bucketWF P h v → bucketWF P h' v
  | .file v h1 h2 h3 => .file v h1 h2 (treeWF_mono hh h3)
  | .inline v h1 h2 h3 h4 => .inline v h1 h2 h3 (pageTreeWF_mono hh h4)
end

/-- `treeOK` holds at a higher mark, the pages, root and txid the same. -/
theorem treeOK_mono {C C' : CommitSt} (H : treeOK C) (hp : C'.pages = C.pages)
    (hr : C'.root = C.root) (hh : C.hwm ≤ C'.hwm) (ht : C'.txid = C.txid) : treeOK C' := by
  obtain ⟨⟨hwf, hs, hk, hpht⟩, htp, hd, hext, hrs, htx⟩ := H
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp, hr]; exact treeWF_mono hh hwf
  · rw [hp]; exact hs
  · rw [hp, hr]; exact hk
  · rw [hp]; exact hpht
  · rw [hp, hr]; exact htp
  · rw [hp]; exact hd
  · intro id pg hpg; rw [hp] at hpg; have := hext id pg hpg; omega
  · rw [hp, hr]; exact hrs
  · rw [ht]; exact htx

/-- `treeData` reads the pages and the root only. -/
theorem treeData_congr {C C' : CommitSt} (hp : C'.pages = C.pages) (hr : C'.root = C.root) :
    treeData C' = treeData C := by
  unfold treeData; rw [hp, hr]

end tree

end bbolt
end EtcdGrove
end Perennial
