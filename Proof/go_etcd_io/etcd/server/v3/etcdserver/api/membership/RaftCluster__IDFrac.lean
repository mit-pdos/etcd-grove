/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__IDFrac.lean` (claim #34
stage 4, 2026-11-25). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__IDFrac

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem membership.RaftCluster.ID.wp_proofFrac :
    membership.RaftCluster.ID.specFrac (GF := GF) (hG := hG) := by
  intro c dq cid
  wp_start as Hcid
  wp_auto
  iapply HΦ
  iexact Hcid

end proof

end EtcdGrove
end Perennial
