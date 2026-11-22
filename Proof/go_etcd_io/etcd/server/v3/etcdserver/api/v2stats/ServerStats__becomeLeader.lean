/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v2stats/ServerStats__becomeLeader.lean`
(`server.go`): the state compared with `StateLeader`, and if it differs, the state, the leader's
name and start time stored in the stats' fields (the caller's, under the mutex).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.ServerStats__becomeLeader
public import Perennial.Spec.time.Now

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Assumptions]

theorem v2stats.ServerStats.becomeLeader.wp_proof (wp_Now : time.Now.spec (GF := GF) (hG := hG)) :
    v2stats.ServerStats.becomeLeader.spec (GF := GF) (hG := hG) := by
  intro ss v
  wp_start as Hv
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ
    iexists v
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
  · (try wp_auto)
    wp_apply wp_Now as %t -
    (try wp_auto)
    iapply HΦ
    iexists _
    iframe
    ipureintro; exact ⟨rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
