/-
`(*membership.RaftCluster).SetVersionChangedNotifier(n)` (`cluster.go`: `c.versionChanged = n`),
verified: translated with its body (`Code/go_etcd_io/etcd/server/v3/etcdserver/api/membership.toml`).
Until 2026-11-18 a trust-boundary axiom (the server-construction unit, stage N0, 2026-10-16).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__SetVersionChangedNotifier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem membership.RaftCluster.SetVersionChangedNotifier.wp_proof :
    membership.RaftCluster.SetVersionChangedNotifier.spec (GF := GF) (hG := hG) := by
  intro c n
  wp_start as ⟨_, %v, Hv⟩
  wp_auto
  iapply HΦ
  iexact Hv

end proof

end EtcdGrove
end Perennial
