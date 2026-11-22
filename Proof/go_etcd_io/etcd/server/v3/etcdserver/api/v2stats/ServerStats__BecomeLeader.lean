/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v2stats/ServerStats__BecomeLeader.lean`
(`server.go`; until prove-ps2-v2stats, 2026-11-21, the trust boundary): `becomeLeader` under the
stats' mutex.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.ServerStats__BecomeLeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.ServerStats__becomeLeader

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

theorem v2stats.ServerStats.BecomeLeader.wp_proof
    (wp_becomeLeader : v2stats.ServerStats.becomeLeader.spec (GF := GF) (hG := hG)) :
    v2stats.ServerStats.BecomeLeader.spec (GF := GF) (hG := hG) := by
  intro st
  wp_start as ⟨%Hnn, #Hss⟩
  iunfold v2stats.isServerStats at Hss
  icases Hss with ⟨%sq, %rq, #Hmu, #Hsq, #Hrq⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold v2stats.ssLockR at HR
  icases HR with ⟨%v, Hv, %Hq⟩
  (try wp_auto)
  wp_apply wp_becomeLeader $$ [$Hv] as ⟨%v', Hv, %Hq'⟩
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hv]
  · inext
    iunfold v2stats.ssLockR
    iexists v'
    iframe
    ipureintro; rw [Hq'.1, Hq'.2]; exact Hq
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
