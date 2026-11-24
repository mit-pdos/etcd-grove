/-
Proof of `membership.WithMaxLearners.spec` (claim #34, stage 2, 2026-11-25): the closure over the
fresh `max`, read-only from its return on.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.WithMaxLearners

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

theorem membership.WithMaxLearners.wp_proof :
    membership.WithMaxLearners.spec (GF := GF) (hG := hG) := by
  intro ml
  wp_start
  wp_auto
  ipersist max
  iapply HΦ
  unfold membership.clusterOptMax
  imodintro
  iintro %p %ml0 %Φ' Hp HΦ'
  wp_auto
  iapply HΦ'
  iexact Hp

end proof

end EtcdGrove
end Perennial
