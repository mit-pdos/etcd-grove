/-
Lean-first (no Rocq counterpart).

# Porcupine: package initialization (2026-10-14)

`github.com/anishathalye/porcupine` (`third_party/porcupine`) has no package-level variable the
checker reads (`prime` and the `CheckResult`s are constants), so its package fact is `True`;
the packages it imports have theirs (Perennial's `context`, `fmt`, `sort`, `strings`, `time`).
-/
module

public import GeneratedProof.github_com.anishathalye.porcupine
public import Proof.github_com.anishathalye.porcupine.Theory
public import Perennial.Proof.context
public import Perennial.Proof.sort
public import Perennial.Proof.time
public import Perennial.Proof.fmt
public import Perennial.Proof.strings

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.anishathalye.porcupine

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.anishathalye.porcupine :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.anishathalye.porcupine :=
  build_get_is_pkg_init_wf

end init

end github_com.anishathalye.porcupine

end Perennial
