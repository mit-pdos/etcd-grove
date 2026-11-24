/-
The package fact of QuePaxa's client messages: `True` (notes/dsv-quepaxa.md).
-/
module

public import Dsverify.GeneratedProof.raxos.proto.client
public import Net.Proof.net.Base
public import Dsverify.Proof.raxos.proto.Base
public import Perennial.Proof.encoding.binary.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.reflect.Base
public import Perennial.Proof.sync.Base
public import Proof.google_golang_org.protobuf.PkgInit

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace raxos.proto.client

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.raxos.proto.client :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.raxos.proto.client :=
  build_get_is_pkg_init_wf

end def_

end raxos.proto.client
end Perennial
