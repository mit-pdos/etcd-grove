/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/NewAuthServer.lean` (item 4, the server
start). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewAuthServer

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.NewAuthServer.wp_proof : v3rpc.NewAuthServer.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  wp_auto
  wp_alloc p as Hp
  ihave %Hpn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  ipersist authenticator
  wp_auto
  iapply HΦ
  iunfold v3rpc.authServerIs
  iframe #
  ipureintro; exact Hpn

end proof

end EtcdGrove
end Perennial
