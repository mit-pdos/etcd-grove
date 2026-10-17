/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/adt/NewInt64Point.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewInt64Point

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

theorem adt.NewInt64Point.wp_proof :
    adt.NewInt64Point.spec (GF := GF) (hG := hG) := by
  intro a
  wp_start
  wp_auto
  wp_if_destruct
  · have h : adt.int64PointEnd (W64 9223372036854775807) = W64 9223372036854775807 := by
      unfold adt.int64PointEnd; rw [ite_eq_left (by decide)]
    rw [h]
    unfold adt.int64Ivl
    wp_end
  · have h : adt.int64PointEnd a = a + W64 1 := by
      unfold adt.int64PointEnd; rw [ite_eq_right (by intro h'; apply Hif; word)]; rfl
    rw [h]
    unfold adt.int64Ivl
    wp_end

end proof

end EtcdGrove
end Perennial
