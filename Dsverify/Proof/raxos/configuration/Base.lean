/-
The package fact of QuePaxa's `configuration`: `True` (notes/dsv-quepaxa.md).
-/
module

public import Dsverify.GeneratedProof.raxos.configuration
public import Net.Proof.net.Base
public import Dsverify.Proof.gopkg_in.yaml_v2.Base
public import Dsverify.Proof.io.ioutil.Base
public import Perennial.Proof.strconv.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace raxos.configuration

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.raxos.configuration :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.raxos.configuration :=
  build_get_is_pkg_init_wf

end def_

end raxos.configuration
end Perennial
