/- Lean-first (no Rocq counterpart).

# `errors.Is` returns on an `*errorString` (`errIsTerm`)

An `errors.New` error is a leaf pointer error without an `Is` method, so `errors.Is(_, u)` on it returns for every
pointer target `u` (`errors.wp_Is_leaf`). Moved out of the WAL's `DecTerm.lean` (2026-11-14, `wal-vsnap4`) so that
package facts (`walpbInit`, `wal.errVar`) state it of their `errors.New` variables.
-/
module

public import LinuxFs.Spec.fmt.ErrorfErrsNot
public import Perennial.Proof.errors.Results
public import Proof.errors.NewVar

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section term
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [errs_sem : _root_.Perennial.errors.Assumptions]

/-- **An `*errorString`'s `errors.Is` returns** on every pointer target. -/
theorem errIsTerm_errorString (x : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.errors ⊢
      errIsTerm (GF := GF) (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) := by
  iintro #Hi
  unfold errIsTerm
  iintro !> %u %hu
  iintro !> %Φ - HΦ
  obtain ⟨hp, hleaf, hIs⟩ := EtcdGrove.errorString_leaf x
  wp_apply (_root_.Perennial.errors.wp_Is_leaf _ u hleaf hIs hu
    (_root_.Perennial.errors.treeTyped_pointer _ u hp))
  iapply HΦ
  itrivial

/-- An `*errorString` is a target `errIsTerm` admits. -/
theorem errorString_ptr (x : Loc) :
    ∀ tii, interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x =
      interface.ok tii → _root_.Perennial.errors.IsPointerError tii := by
  intro tii ht
  cases ht
  exact ⟨_, x, rfl, rfl⟩

end term

end EtcdGrove
end Perennial

end
