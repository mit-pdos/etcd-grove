/-
The example `k8s/compactor` (`examples/k8s/compactor`, Kubernetes' etcd compactor run as API servers
run it: K3 of `notes/k8s-compactor-plan.md`): its package fact. The package has no package variable
and no `init()`: its fact is `True`, and its initializer initializes its imports, among them the
etcd3 store's packages and `util/feature` (`featureInit`, `Proof/k8s_io/apiserver/pkg/storage/etcd3/Base.lean`).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.k8s.compactor

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst [EtcdGrove.k8s.CompactorRegistry] :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.compactor :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst [EtcdGrove.k8s.CompactorRegistry] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.compactor :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.k8s.compactor
end Perennial
