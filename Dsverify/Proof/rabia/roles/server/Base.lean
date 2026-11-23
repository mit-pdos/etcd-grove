/-
The package fact of `rabia.roles.server`: `True` (no package-level state yet (notes/dsv-rabia.md: the lab's facts are to be ported)).
-/
module

public import Dsverify.GeneratedProof.rabia.roles.server
public import Net.Proof.net.Base
public import Dsverify.Proof.github_com.rs.zerolog.Base
public import Dsverify.Proof.rabia.internal.config.Base
public import Dsverify.Proof.rabia.internal.ledger.Base
public import Dsverify.Proof.rabia.internal.logger.Base
public import Dsverify.Proof.rabia.internal.message.Base
public import Dsverify.Proof.rabia.internal.system.Base
public import Dsverify.Proof.rabia.roles.server.layers.consensus.Base
public import Dsverify.Proof.rabia.roles.server.layers.network.Base
public import Dsverify.Proof.rabia.roles.server.layers.proxy.Base
public import Perennial.Proof.fmt.Base
public import Proof.os.PkgInit
public import Perennial.Proof.sync.Base
public import Perennial.Proof.time.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace rabia.roles.server

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.rabia.roles.server :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.rabia.roles.server :=
  build_get_is_pkg_init_wf

end def_

end rabia.roles.server
end Perennial
