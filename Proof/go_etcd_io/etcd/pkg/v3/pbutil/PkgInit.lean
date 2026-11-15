/-
The package-initialization instance of `pkg/v3/pbutil`: fact `True` (names only). One home, shared by the server's
`Base.lean` files and the WAL (until 2026-11-15 declared in the apply layer's `Base.lean` and the WAL's `DepsPkgInit.lean`; notes/wal-lean-integration.md).
-/
module

public import GeneratedProof.go_etcd_io.etcd.pkg.v3.pbutil
public import Perennial.Proof.ProofPrelude

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace go_etcd_io.etcd.pkg.v3.pbutil

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.pbutil

end init

end Perennial
