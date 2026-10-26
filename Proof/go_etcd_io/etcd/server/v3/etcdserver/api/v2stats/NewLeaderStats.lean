/-
`v2stats.NewLeaderStats(lg, id)` (`leader.go`), translated since 2026-10-22 (names-only, the trust
boundary, until then). Lean-first (no Rocq counterpart); the
server-construction unit, stage N0 (2026-10-16), for `NewServer`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.NewLeaderStats
public import Spec.go_uber_org.zap.NewNop

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.Assumptions]

/-- The logger defaulted to `zap.NewNop()` when nil, the followers' map made, the stats
allocated. -/
theorem v2stats.NewLeaderStats.wp_proof (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG)) :
    v2stats.NewLeaderStats.spec (GF := GF) (hG := hG) := by
  intro lg id
  wp_start
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  (try wp_auto)
  wp_if_destruct
  all_goals
    try wp_apply wp_NewNop as %l _
    (try wp_auto)
    wp_apply wp_map_make1 as %m _
    (try wp_auto)
    wp_alloc p as Hp
    (try wp_auto)
    ihave %Hnn := typedPointsto_not_null $$ Hp
    iapply HΦ
    ipureintro; exact Hnn

end proof

end EtcdGrove
end Perennial
