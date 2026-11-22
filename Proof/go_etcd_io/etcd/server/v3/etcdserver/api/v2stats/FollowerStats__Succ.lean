/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v2stats/FollowerStats__Succ.lean`
(`leader.go`; prove-ps2-succ, 2026-11-22: until then the trust boundary): under the stats' mutex,
the success count incremented and the latencies updated (IEEE 754 float steps, `math.Sqrt`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.FollowerStats__Succ
public import Perennial.Spec.math.Sqrt
public import Perennial.Golang.Theory.Float

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

theorem v2stats.FollowerStats.Succ.wp_proof
    (wp_Sqrt : math.Sqrt.spec (GF := GF) (hG := hG)) :
    v2stats.FollowerStats.Succ.spec (GF := GF) (hG := hG) := by
  intro fs d
  wp_start as #Hmu
  iunfold v2stats.isFollowerStats at Hmu
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hmath : isPkgInit (PROP := IProp GF) pkg_id.math $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, %c, %l, Hc, Hl⟩
  (try wp_auto)
  -- `total`, `totalSquare`, `Current`
  wp_apply wp_float64_mul as %tot -
  (try wp_auto)
  wp_apply wp_float64_mul as %tsq -
  (try wp_auto)
  wp_apply wp_float64_div as %cur -
  (try wp_auto)
  -- `Current > Maximum`, `Current < Minimum`
  generalize (float64Leb l.Maximum' cur && !float64Eq cur l.Maximum') = b1
  cases b1
  all_goals (
    (try wp_auto)
    generalize (float64Leb cur l.Minimum' && !float64Eq cur l.Minimum') = b2
    cases b2
    all_goals (
      (try wp_auto)
      -- the averages and the standard deviation
      repeat (first
        | wp_apply wp_float64_add as %_ -
        | wp_apply wp_float64_sub as %_ -
        | wp_apply wp_float64_mul as %_ -
        | wp_apply wp_float64_div as %_ -
        | wp_apply wp_Sqrt as %_ -
        | wp_auto)
      -- the deferred `Unlock`
      wp_method_call
      wp_call
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hc Hl]
      · inext; iexists _, _; iframe
      (try wp_auto)
      iapply HΦ
      itrivial))

end proof

end EtcdGrove
end Perennial
