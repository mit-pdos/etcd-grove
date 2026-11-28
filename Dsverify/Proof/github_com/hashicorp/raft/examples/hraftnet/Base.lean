/-
The package fact of the hraft kit's `examples/hraftnet` (notes/dsv-hraft.md): `True` (no package variables).
-/
module

public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet
public import Net.Proof.net.Base
public import Perennial.Proof.errors.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.time.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base
public import Proof.github_com.anishathalye.porcupine.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Base
public import Dsverify.Proof.github_com.hashicorp.raft.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.snapstore.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.service.Base
public import Net.Proof.net.rpc.PkgInit
public import Net.Proof.net.http.PkgInit

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.hashicorp.raft.examples.hraftnet

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet :=
  build_get_is_pkg_init_wf

end def_

end github_com.hashicorp.raft.examples.hraftnet
end Perennial
