/-
Lean-first (no Rocq counterpart).

# lintest/perclient: package initialization (2026-11-22)

`examples/lib/lintest/perclient/perclient.go` has no package-level variable, so its package fact
is `True`; the packages it imports have theirs (lintest's, porcupine's, Perennial's `sync` and
`time`).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient

end Perennial
