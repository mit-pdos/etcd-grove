/-
zerolog's `New(nil)` and `Nop()` (`log.go`; dsv-retire-3, 2026-11-26, mit-pdos/etcd-grove#49 step 3), from
the translation: `New` puts `ioutil.Discard` in place of the `nil` writer, keeps it if it is a
`LevelWriter` and wraps it in a `levelWriterAdapter` otherwise. `Nop()` is `New(nil).Level(Disabled)`;
zerolog's initializer runs it (`disabledLogger`), `New.wp_proof` is `wp_New_nil`.
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.rs.zerolog

section def_
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

/-- The writer `New(w)` gives its logger for a non-`nil` writer `w` (`log.go`): `w` itself if it is a
`LevelWriter`, else `w` wrapped in a `levelWriterAdapter`. -/
def newLevelWriter (w : GoInterface) : GoInterface :=
  match w with
  | GoInterface.ok ii =>
    if go.typeSetContains ii.ty LevelWriter.ty = true then w
    else interface.mkOk levelWriterAdapter.ty #({ Writer' := w } : levelWriterAdapter)
  | GoInterface.nil => interface.mkOk levelWriterAdapter.ty #({ Writer' := w } : levelWriterAdapter)

/-- The logger `New` returns for the writer `w` (`New(nil)`: `w` is `ioutil.Discard`'s value). -/
def newLogger (w : GoInterface) : Logger :=
  { w' := newLevelWriter w, level' := W8 (-1), sampler' := GoInterface.nil, context' := slice.nil,
    hooks' := slice.nil, stack' := false }

end def_

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : github_com.rs.zerolog.Assumptions]

theorem wp_New_nil (w : GoInterface) :
    {{ (globalAddr _root_.Perennial.io.ioutil.Discard ↦□ w : IProp GF) }}
      (App (Val (@! New)) (Val #interface.nil))
    {{ RET #(newLogger w); True }} := by
  wp_start as #HDis
  wp_auto
  cases w with
  | nil =>
    simp only
    wp_auto
    simp only [newLogger, newLevelWriter]
    iapply HΦ
    itrivial
  | ok ii =>
    simp only
    by_cases hlw : go.typeSetContains ii.ty LevelWriter.ty = true
    · simp only [hlw]
      wp_auto
      simp only [newLogger, newLevelWriter, hlw, ↓reduceIte]
      iapply HΦ
      itrivial
    · simp only [hlw]
      wp_auto
      simp only [newLogger, newLevelWriter, hlw, Bool.false_eq_true, ↓reduceIte]
      iapply HΦ
      itrivial

/-- `Nop()` (`log.go`): `New(nil).Level(Disabled)`, a logger. -/
theorem wp_Nop (w : GoInterface) :
    {{ (globalAddr _root_.Perennial.io.ioutil.Discard ↦□ w : IProp GF) }}
      (App (Val (@! Nop)) (Val #()))
    {{ (lg : Logger), RET #lg; True }} := by
  wp_start as #HDis
  wp_auto
  wp_apply (wp_New_nil w) $$ HDis
  try wp_auto
  unfold Disabled
  wp_method_call
  wp_call
  wp_auto
  iapply HΦ
  itrivial

end proof

end github_com.rs.zerolog
end Perennial
