/-
The package-initialization instance of `server/v3/storage/datadir`: fact `True` (its functions read no
package variable; its constants are folded by goose). bkarea, 2026-11-22: `config` imports it since
`ServerConfig.BackendPath` is translated (`datadir.ToBackendFileName`).
-/
module

public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.datadir
public import Perennial.Proof.ProofPrelude
public import Proof.path.filepath.PkgInit

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

namespace go_etcd_io.etcd.server.v3.storage.datadir

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.datadir :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.datadir :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage.datadir

end init

end Perennial
