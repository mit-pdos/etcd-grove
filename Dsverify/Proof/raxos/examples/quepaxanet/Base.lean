/-
The package fact of the QuePaxa kit: `True` (notes/dsv-quepaxa.md).
-/
module

public import Dsverify.GeneratedProof.raxos.examples.quepaxanet
public import Net.Proof.net.Base
public import Dsverify.Proof.raxos.configuration.Base
public import Dsverify.Proof.raxos.proto.client.Base
public import Dsverify.Proof.raxos.replica.src.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Base
public import Perennial.Proof.encoding.binary.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.log.Base
public import Perennial.Proof.strings.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.time.Base
public import Proof.bufio.PkgInit
public import Proof.github_com.anishathalye.porcupine.Base
public import Proof.math.rand.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace raxos.examples.quepaxanet

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.raxos.examples.quepaxanet :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.raxos.examples.quepaxanet :=
  build_get_is_pkg_init_wf

end def_

end raxos.examples.quepaxanet
end Perennial
