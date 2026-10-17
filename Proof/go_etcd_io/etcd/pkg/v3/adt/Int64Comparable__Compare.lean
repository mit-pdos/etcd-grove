/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/adt/Int64Comparable__Compare.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.Int64Comparable__Compare

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.Int64Comparable.Compare.wp_proof :
    adt.Int64Comparable.Compare.spec (GF := GF) (hG := hG) := by
  intro v w
  wp_start
  wp_auto
  wp_if_destruct
  · have h : adt.int64Cmp v w = -1 := by unfold adt.int64Cmp; rw [ite_eq_left Hif]
    rw [h]
    wp_end
  · wp_if_destruct
    · have h : adt.int64Cmp v w = 1 := by
        unfold adt.int64Cmp; rw [ite_eq_right (by omega), ite_eq_left Hif]
      rw [h]
      wp_end
    · have h : adt.int64Cmp v w = 0 := by
        unfold adt.int64Cmp; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [h]
      wp_end

end proof

end EtcdGrove
end Perennial
