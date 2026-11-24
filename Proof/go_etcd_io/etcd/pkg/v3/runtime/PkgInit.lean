/-
The package-initialization instance of etcd's `go.etcd.io/etcd/pkg/v3/runtime` (`FDUsage`, `FDLimit`
trusted, `TrustedCode/go_etcd_io/etcd/pkg/v3/runtime.lean`). Its fact is `True`: the package has no
variables. Its `wp_initialize'` is `Init.lean` (generated, `etc/gen-init.py`).
-/
module

public import GeneratedProof.go_etcd_io.etcd.pkg.v3.runtime
public import Perennial.Proof.ProofPrelude
public import Proof.os.PkgInit
public import Proof.syscall.PkgInit

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace go_etcd_io.etcd.pkg.v3.runtime

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.runtime :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.runtime :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.runtime

end init

end Perennial
