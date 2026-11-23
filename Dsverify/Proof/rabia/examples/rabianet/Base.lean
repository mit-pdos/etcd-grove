/-
The package fact of `rabia.examples.rabianet`: `True` (no package-level state yet (notes/dsv-rabia.md: the lab's facts are to be ported)).
-/
module

public import Dsverify.GeneratedProof.rabia.examples.rabianet
public import Dsverify.Proof.rabia.internal.config.Base
public import Dsverify.Proof.rabia.internal.message.Base
public import Dsverify.Proof.rabia.internal.tcp.Base
public import Dsverify.Proof.rabia.roles.server.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.log.Base
public import Proof.math.rand.Base
public import Net.Proof.net.Base
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.time.Base
public import Proof.github_com.anishathalye.porcupine.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace rabia.examples.rabianet

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.rabia.examples.rabianet :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.rabia.examples.rabianet :=
  build_get_is_pkg_init_wf

end def_

end rabia.examples.rabianet
end Perennial
