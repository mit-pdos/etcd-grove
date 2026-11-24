/-
The package fact of QuePaxa's `proto`: `True` (notes/dsv-quepaxa.md).
-/
module

public import Dsverify.GeneratedProof.raxos.proto
public import Net.Proof.net.Base
public import Perennial.Proof.io.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace raxos.proto

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.raxos.proto :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.raxos.proto :=
  build_get_is_pkg_init_wf

end def_

end raxos.proto
end Perennial
