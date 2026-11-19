/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__SetVersionChangedNotifier.lean`.
Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16), for
`NewServer`; an axiom until 2026-11-19 (prove-membership), now proved on the translated body.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__SetVersionChangedNotifier

@[expose] public section

set_option linter.unusedSectionVars false

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
  wp_start as ⟨-, %v, Hv⟩
  wp_auto
  iapply HΦ
  iexact Hv

end proof

end EtcdGrove
end Perennial
