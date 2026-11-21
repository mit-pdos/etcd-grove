/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__clearLeaseExpiredNotifier.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__clearLeaseExpiredNotifier
public import Spec.go_etcd_io.etcd.server.v3.lease.newLeaseExpiredNotifier

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.clearLeaseExpiredNotifier.wp_proof
    (wp_new : lease.newLeaseExpiredNotifier.spec (GF := GF) (hG := hG)) :
    lease.lessor.clearLeaseExpiredNotifier.spec (GF := GF) (hG := hG) := by
  intro lp np
  wp_start as Hn
  (try wp_auto)
  wp_apply wp_new as %np' Hnot
  (try wp_auto)
  iapply HΦ
  iexists np'
  iframe

end proof

end EtcdGrove
end Perennial
