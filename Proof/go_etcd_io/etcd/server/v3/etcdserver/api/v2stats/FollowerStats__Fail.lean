/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v2stats/FollowerStats__Fail.lean`
(`leader.go`; prove-ps2, 2026-11-21: until then the trust boundary): under the stats' mutex, the
failure count incremented.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.FollowerStats__Fail

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

theorem v2stats.FollowerStats.Fail.wp_proof :
    v2stats.FollowerStats.Fail.spec (GF := GF) (hG := hG) := by
  intro fs
  wp_start as #Hmu
  iunfold v2stats.isFollowerStats at Hmu
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, %c, %l, Hc, Hl⟩
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hc Hl]
  · inext; iexists _, _; iframe
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
