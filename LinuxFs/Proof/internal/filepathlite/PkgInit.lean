/-
The package fact of `internal/filepathlite` (the part's translation): no fact (its lexical functions read no package variable). WAL leaf specs, 2026-11-13.
-/
module

public import LinuxFs.GeneratedProof.internal.filepathlite
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.internal.stringslite
public import Perennial.Proof.errors

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace internal.filepathlite

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.filepathlite :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.filepathlite :=
  build_get_is_pkg_init_wf

end internal.filepathlite

end init

end Perennial
