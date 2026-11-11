/- Lean-first (no Rocq counterpart). The proof of `noCluster.Version`: Draft, to come.

The outline: `return nil`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.noCluster__Version

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem noCluster.Version.wp_proof :
    noCluster.Version.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  iapply HΦ
  ipureintro; rfl


end proof

end mvccfull
end EtcdGrove
end Perennial
