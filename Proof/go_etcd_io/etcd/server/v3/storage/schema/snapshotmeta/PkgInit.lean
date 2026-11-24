/- The frozen metadata readers have no package variables or init functions. -/
module
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.schema.snapshotmeta
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.PkgInit

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace go_etcd_io.etcd.server.v3.storage.schema.snapshotmeta
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema.snapshotmeta :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst [EtcdGrove.prometheus.PromRegGS GF] : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema.snapshotmeta :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage.schema.snapshotmeta
end Perennial
