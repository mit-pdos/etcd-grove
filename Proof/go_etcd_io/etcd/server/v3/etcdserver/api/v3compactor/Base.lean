/-
Package initialization instance of `server/v3/etcdserver/api/v3compactor` (the auto-compactor), here rather than in the server's `BaseApply.lean`
(the spec-first pilot's freeze, 2026-10-27: so that the package's definitions do not import the
server's). An assumption about package initialization, `True` (no variable its proofs read).
-/
module

public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor
public import Proof.github_com.jonboulle.clockwork.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor

end init

end Perennial
