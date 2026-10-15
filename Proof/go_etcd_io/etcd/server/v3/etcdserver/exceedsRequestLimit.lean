/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/exceedsRequestLimit.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.exceedsRequestLimit
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.isPriorityRequest

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem exceedsRequestLimit.wp_proof (hP : isPriorityRequest.spec (GF := GF) (hG := hG)) :
    exceedsRequestLimit.spec (GF := GF) (hG := hG) := by
  intro ai ci p rq enable
  wp_start as #Hirr
  wp_auto
  wp_if_destruct
  · have h : exceedsLimit ai ci rq.leaseRevoke.isSome enable = false := by
      unfold exceedsLimit; rw [if_pos Hif]
    rw [h]
    iapply HΦ
    itrivial
  · have hn : ¬ uint.Z ci ≤ uint.Z (ai + W64 5000) := by simpa using Hif
    cases enable
    · (try wp_auto)
      have h : exceedsLimit ai ci rq.leaseRevoke.isSome false = true := by
        unfold exceedsLimit; rw [ite_eq_right_iff.mpr (fun h => absurd h hn)]; simp
      rw [h]
      iapply HΦ
      itrivial
    · (try wp_auto)
      wp_apply hP p rq $$ []
      · iframe #
      cases hlr : rq.leaseRevoke.isSome
      · (try wp_auto)
        have h : exceedsLimit ai ci false true = true := by
          unfold exceedsLimit; rw [ite_eq_right_iff.mpr (fun h => absurd h hn)]; simp
        rw [h]
        iapply HΦ
        itrivial
      · (try wp_auto)
        wp_if_destruct
        · have h : exceedsLimit ai ci true true = false := by
            unfold exceedsLimit; rw [ite_eq_right_iff.mpr (fun h => absurd h hn)]
            simp only [Bool.true_and, decide_eq_true_eq]; rw [if_pos Hif]
          rw [h]
          iapply HΦ
          itrivial
        · (try wp_auto)
          have h : exceedsLimit ai ci true true = true := by
            unfold exceedsLimit; rw [ite_eq_right_iff.mpr (fun h => absurd h hn)]; simp only [Bool.and_true, Bool.true_and]
            rw [if_neg (by simpa using Hif)]
          rw [h]
          iapply HΦ
          itrivial

end proof

end EtcdGrove
end Perennial

