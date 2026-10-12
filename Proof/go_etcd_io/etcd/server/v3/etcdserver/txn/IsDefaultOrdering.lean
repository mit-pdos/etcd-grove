/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.IsDefaultOrdering

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.IsDefaultOrdering.wp_proof : txn.IsDefaultOrdering.spec (GF := GF) (hG := hG) := by
  intro target order
  wp_start
  wp_auto
  wp_if_destruct
  · rw [show decide (True ∨ target = W32 0 ∧ W32 0 = W32 1) = true by simp]
    wp_end
  · rename_i Hif
    wp_if_destruct
    · simp only [Hif, _root_.false_or, _root_.true_and]
      iapply HΦ; itrivial
    · rename_i Hif2
      simp only [Hif, Hif2, _root_.false_or, _root_.false_and, decide_false]
      iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
