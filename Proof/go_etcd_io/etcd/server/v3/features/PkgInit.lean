/-
The package fact of `server/v3/features` (`featuresInit`, `Defs.lean`; featuregate-3, 2026-11-23:
until then `True`, in `etcdserver/BaseApply.lean`): `DefaultEtcdServerFeatureGates` holds a read-only
map of the server's features.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.features.Defs
public import Proof.go_etcd_io.etcd.pkg.v3.featuregate.PkgInit

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

namespace go_etcd_io.etcd.server.v3.features

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features :=
  define_is_pkg_init EtcdGrove.featuresInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.features

end init

end Perennial
