/-
The `cellmint` example (`examples/axiomcx/cellmint`): its package fact.

`cellmint` has no package variable and no `init()`: its fact is `True`, and its initializer
initializes its one import, `sync`.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint
end Perennial
