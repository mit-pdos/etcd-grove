/-
The string-affine instance of the comparator abstraction (the auth plan's S2b, 2026-10-23):
`strKey`'s comparison contract from `StringAffineComparable.Compare`'s spec (`strKey_ok`), and the
string-affine forms of the generic results' resources (a lent `iv` is the entry's `IntervalValue`,
`strKey_ivAt`, under a big separating conjunction). What the string-affine wrappers of the
generic proofs (`intervalTree__Insert.lean`, ...) use. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.NodeLemmas
public import Spec.go_etcd_io.etcd.pkg.v3.adt.StringAffineComparable__Compare

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section strkey
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- **The comparison contract of string-affine keys**, from `StringAffineComparable.Compare`'s
spec. -/
theorem strKey_ok (h : adt.StringAffineComparable.Compare.spec (GF := GF) (hG := hG)) :
    (strKey (GF := GF)).CompareOk := by
  intro d d' v v' k k'
  simp only [strKey_keyAt, strKey_ty]
  iintro %Φ ⟨#Hpkg, %Hv, %Hv'⟩ HΦ
  subst Hv Hv'
  wp_apply h k k' $$ []
  (try iapply HΦ)
  isplitl [] <;> ipureintro <;> rfl

/-- The lent `iv` fields over string-affine keys are the entries' `IntervalValue`s. -/
theorem strKey_bigSep_ivAt (l : List (Loc × Entry)) (dq : DFrac) :
    ([∗list] x ∈ l, (strKey (GF := GF)).ivAt x.1 dq x.2) ⊣⊢
      [∗list] x ∈ l, x.1 ↦{dq} ({ Ivl' := affIvl x.2.1.1 x.2.1.2, Val' := x.2.2 } : IntervalValue) := by
  constructor
  · iintro H
    iapply (BigSepL.bigSepL_mono_of_forall (PROP := IProp GF) (l := l)
      (Φ := fun _ x => (strKey (GF := GF)).ivAt x.1 dq x.2)
      (Ψ := fun _ x => x.1 ↦{dq} ({ Ivl' := affIvl x.2.1.1 x.2.1.2, Val' := x.2.2 } : IntervalValue))
      (fun {_ x} => (strKey_ivAt x.1 dq x.2).1)) $$ H
  · iintro H
    iapply (BigSepL.bigSepL_mono_of_forall (PROP := IProp GF) (l := l)
      (Φ := fun _ x => x.1 ↦{dq} ({ Ivl' := affIvl x.2.1.1 x.2.1.2, Val' := x.2.2 } : IntervalValue))
      (Ψ := fun _ x => (strKey (GF := GF)).ivAt x.1 dq x.2)
      (fun {_ x} => (strKey_ivAt x.1 dq x.2).2)) $$ H

/-- The same, with the pointers' non-nullness (`Stab`'s post). -/
theorem strKey_bigSep_ivAt_nn (l : List (Loc × Entry)) (dq : DFrac) :
    ([∗list] x ∈ l, ⌜x.1 ≠ null⌝ ∗ (strKey (GF := GF)).ivAt x.1 dq x.2) ⊢
      [∗list] x ∈ l, ⌜x.1 ≠ null⌝ ∗
        x.1 ↦{dq} ({ Ivl' := affIvl x.2.1.1 x.2.1.2, Val' := x.2.2 } : IntervalValue) := by
  iintro H
  iapply (BigSepL.bigSepL_mono_of_forall (PROP := IProp GF) (l := l)
    (Φ := fun _ x => iprop(⌜x.1 ≠ null⌝ ∗ (strKey (GF := GF)).ivAt x.1 dq x.2))
    (Ψ := fun _ x => iprop(⌜x.1 ≠ null⌝ ∗
      x.1 ↦{dq} ({ Ivl' := affIvl x.2.1.1 x.2.1.2, Val' := x.2.2 } : IntervalValue)))
    (fun {_ x} => by
      iintro ⟨%h, Hx⟩
      icases (strKey_ivAt _ _ _).1 $$ Hx with Hx
      iframe
      ipureintro; exact h)) $$ H

end strkey

end adt
end EtcdGrove
end Perennial
