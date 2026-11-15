/-
A reader cursor's position after a move (maintainer R, U6g item 1): what `boltCurDef`'s reader
branch (`rCurPos`) needs of `first`'s result (`rCurKV … 0`), the empty bucket included.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__next_r

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section curPos
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit package_sem in
/-- `next`'s target is the position or one more (`rPosF_s`). -/
theorem rPosAt_s {v : View} {bv : List w8} {pp : Loc} {els : List elemRef} {i s : Nat}
    (h : rPosAt v bv pp els i s) : s = i ∨ s = i + 1 :=
  rPosF_s _ _ _ _ _ h

omit package_sem in
/-- **`first`'s cursor** (`rCurKV … 0`) is at entry `0` (`rCurPos … (some 0)`): on the first
entry, or past the entries of an empty bucket at a stack from which `next` goes to `0`. -/
theorem rCurKV_first_pos (v : View) (bv : List w8) (pp : Loc) (els : List elemRef)
    (k vl : GoSlice) (fl : w32) :
    rCurKV (GF := GF) v bv pp els 0 k vl fl ⊢ ⌜rCurPos v bv pp els (some 0)⌝ := by
  unfold rCurKV
  iintro (⟨%pg, %idx, %H, -⟩ | %H)
  · ipureintro; exact Or.inl ⟨1, H.1, fun h => by omega⟩
  · ipureintro
    obtain ⟨hl, -, -, -, i, hi⟩ := H
    rcases rPosAt_s hi with h | h
    · subst h; exact Or.inl ⟨0, hi, fun _ => by omega⟩
    · omega

end curPos

end bbolt
end EtcdGrove
end Perennial
