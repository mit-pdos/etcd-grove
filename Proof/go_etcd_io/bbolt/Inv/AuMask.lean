/-
**The mask of a commit point inside an atomic update over `⊤ \ ↑N`** (W5, moved here by W6): the
mask inside (`closeMask N`, the database's namespace), its crash invariant's namespace in it, and the
update's opening and closing from and to `⊤`. `DB.Close.specC`'s and `Open.specC`'s commit points.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.BFile

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
open Iris Iris.BI Iris.ProofMode

section mask
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The mask inside `Close`'s commit point: the database's namespace (`⊤` less the outer mask of
`DB.Close.specC`'s update). -/
abbrev closeMask (N : Namespace) : CoPset := (⊤ : CoPset) \ ((⊤ : CoPset) \ ↑N)

theorem crash_sub_closeMask (N : Namespace) : (↑(N .@ "crash") : CoPset) ⊆ closeMask N := by
  intro x hx
  refine CoPset.in_diff.2 ⟨CoPset.subseteq_top x hx, fun hp => ?_⟩
  exact (CoPset.in_diff.1 hp).2 (nclose_subseteq N "crash" x hx)

open Iris.Std in
/-- An update over `⊤ \ ↑N` opened from `⊤`: the mask inside is `N`'s (as `Fs.fupd_open_au`). -/
theorem fupd_open_closeMask (N : Namespace) (P : IProp GF) :
    (|={(⊤ : CoPset) \ ↑N, ∅}=> P) ⊢ |={⊤, closeMask N}=> P := by
  show _ ⊢ |={⊤, (⊤ : CoPset) \ ((⊤ : CoPset) \ ↑N)}=> P
  have h := fupd_mask_frame_right (P := P) (E1 := (⊤ : CoPset) \ ↑N) (E2 := ∅)
    (Ef := (⊤ : CoPset) \ ((⊤ : CoPset) \ ↑N)) LawfulSet.disjoint_diff_right
  rwa [LawfulSet.subset_union_diff (s₁ := (⊤ : CoPset) \ ↑N) (s₂ := (⊤ : CoPset))
    (fun _ _ => CoPset.mem_full), LawfulSet.union_empty_left] at h

open Iris.Std in
/-- The update's closing, from `N`'s mask back to `⊤` (as `Fs.fupd_close_au`). -/
theorem fupd_close_closeMask (N : Namespace) (P : IProp GF) :
    (|={∅, (⊤ : CoPset) \ ↑N}=> P) ⊢ |={closeMask N, ⊤}=> P := by
  show _ ⊢ |={(⊤ : CoPset) \ ((⊤ : CoPset) \ ↑N), ⊤}=> P
  have h := fupd_mask_frame_right (P := P) (E1 := ∅) (E2 := (⊤ : CoPset) \ ↑N)
    (Ef := (⊤ : CoPset) \ ((⊤ : CoPset) \ ↑N)) LawfulSet.disjoint_empty_left
  rwa [LawfulSet.union_empty_left, LawfulSet.subset_union_diff (s₁ := (⊤ : CoPset) \ ↑N)
    (s₂ := (⊤ : CoPset)) (fun _ _ => CoPset.mem_full)] at h

end mask

end bbolt
end EtcdGrove
end Perennial
