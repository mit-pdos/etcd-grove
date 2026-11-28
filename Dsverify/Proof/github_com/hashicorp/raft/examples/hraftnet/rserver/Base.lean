/-
The package fact of the hraft kit's restartable server machine `examples/hraftnet/rserver`
(hraft_robust; notes/dsv-hraft.md): `True` (no package variables).
-/
module

public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet.rserver
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Base
public import Dsverify.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.PkgInit

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.hashicorp.raft.examples.hraftnet.rserver

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rserver :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rserver :=
  build_get_is_pkg_init_wf

end def_

end github_com.hashicorp.raft.examples.hraftnet.rserver
end Perennial
