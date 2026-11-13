/-
The package fact of `bufio` (the part's translation): no fact (`Reader.Read`'s `panic(errNegativeRead)` is unreachable under the reader's contract, so nothing needs its value). WAL leaf specs, 2026-11-13.
-/
module

public import LinuxFs.GeneratedProof.bufio
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.io
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

namespace bufio

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.bufio :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.bufio :=
  build_get_is_pkg_init_wf

end bufio

end init

end Perennial
