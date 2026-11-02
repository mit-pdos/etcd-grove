/-
Lean-first (no Rocq counterpart).

# gokv's `trusted_proph`: package initialization (2026-10-30)

`github.com/mit-pdos/gokv/trusted_proph` has no package-level variable, so its package fact is
`True`; the package it imports, `primitive`, has its own.
-/
module

public import GeneratedProof.github_com.mit_pdos.gokv.trusted_proph
public import Perennial.Proof.github_com.goose_lang.primitive.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.gokv.trusted_proph

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.gokv.trusted_proph.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.gokv.trusted_proph :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.gokv.trusted_proph :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.gokv.trusted_proph

end Perennial
