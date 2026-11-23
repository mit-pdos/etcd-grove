/-
The package fact of `rabia.roles.server.layers.network`: `True` (no package-level state yet (notes/dsv-rabia.md: the lab's facts are to be ported)).
-/
module

public import Dsverify.GeneratedProof.rabia.roles.server.layers.network
public import Net.Proof.net.Base
public import Dsverify.Proof.rabia.internal.config.Base
public import Dsverify.Proof.rabia.internal.message.Base
public import Dsverify.Proof.rabia.internal.tcp.Base
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace rabia.roles.server.layers.network

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.rabia.roles.server.layers.network :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.rabia.roles.server.layers.network :=
  build_get_is_pkg_init_wf

end def_

end rabia.roles.server.layers.network
end Perennial
