/-
The Kubernetes distributed driver's package (`examples/k8s/dist`): its package fact (k8s-dist K9 step 5,
for `CheckShared`). The package has no package variable and no `init()`: its fact is `True`, and its
initializer initializes its imports, among them the etcd3 driver's (`examples/k8s/etcd3`), the
compactor's and the distributed etcd's packages.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.k8s.dist
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Base
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Base
public import Proof.go_uber_org.zap.PkgInit
public import Proof.github_com.anishathalye.porcupine.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.k8s.dist

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst [EtcdGrove.k8s.CompactorRegistry] :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.dist :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst [EtcdGrove.k8s.CompactorRegistry] [EtcdGrove.prometheus.PromRegGS GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.dist :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.k8s.dist

end Perennial
