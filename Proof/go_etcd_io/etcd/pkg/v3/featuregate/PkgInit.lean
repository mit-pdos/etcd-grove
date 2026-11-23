/-
The package fact of etcd's `featuregate` (`featuregateInit`, `Defs.lean`; featuregate-3, 2026-11-23:
until then `True`, in `etcdserver/apply/Base.lean`): `defaultFeatures`, which `New` clones, holds a
read-only map of `AllAlpha` and `AllBeta`, and `specialFeatures`, which `New` stores in the gate, some
map.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.featuregate.Defs
public import Proof.flag.PkgInit
public import Proof.go_uber_org.zap.PkgInit
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.maps.Base

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace go_etcd_io.etcd.pkg.v3.featuregate

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.featuregate :=
  define_is_pkg_init EtcdGrove.featuregate.featuregateInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.featuregate :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.featuregate

end init

end Perennial
