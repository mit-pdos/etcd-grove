/-
The package fact of `client/pkg/v3/verify`: `True` (WAL W6, 2026-11-13). Its imports' instances
(2026-11-20: `os` and `strings` too, which `Verify`'s translated body calls).
-/
module

public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.verify
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.fmt
public import Perennial.Proof.strings
public import Proof.os.PkgInit

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

namespace go_etcd_io.etcd.client.pkg.v3.verify

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.client.pkg.v3.verify

end init

end Perennial
