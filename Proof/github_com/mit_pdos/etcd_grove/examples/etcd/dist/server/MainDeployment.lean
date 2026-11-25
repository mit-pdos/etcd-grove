/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/server/MainDeployment.lean` (N5).
Lean-first (no Rocq counterpart).

`MainDeployment(d, i)`: `MainDeploymentLogger(d, i, zap.NewNop())`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MainDeployment
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MainDeploymentLogger
public import Spec.go_uber_org.zap.NewNop

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace server

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem MainDeployment.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_MainDeploymentLogger : MainDeploymentLogger.spec (GF := GF) (hG := hG)) :
    MainDeployment.spec (GF := GF) (hG := hG) := by
  intro CS π TB RB v d i m ps ctxs boot Hm Hauth Hfips Hbf Hbgo HLv Haf Hbuq Hrf Hdbo Hms
  wp_start as ⟨Htok, #Hrepr, #Hvoff, Hwa, Hshare⟩
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  (try wp_auto)
  wp_apply (wp_MainDeploymentLogger v d i m lg ps ctxs boot Hm Hauth Hfips Hbf Hbgo HLv Haf Hbuq Hrf
      Hdbo Hms) $$ [Htok Hwa Hshare]
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end server
end etcd_dist
end EtcdGrove
end Perennial

end
