/-
Proof of `Spec/.../mvcc/Revision__GreaterThan.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Revision__GreaterThan

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.Revision.GreaterThan.wp_proof : mvcc.Revision.GreaterThan.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  wp_auto
  wp_if_destruct
  · rw [mvcc.Rev.gt_true_of_main_lt (a := mvcc.revOf a) (b := mvcc.revOf b) Hif]
    wp_end
  · wp_if_destruct
    · rw [mvcc.Rev.gt_false_of_main_lt (a := mvcc.revOf a) (b := mvcc.revOf b) Hif]
      wp_end
    · rw [mvcc.Rev.gt_of_main_eq (a := mvcc.revOf a) (b := mvcc.revOf b)
        (by show a.Main' = b.Main'; word)]
      simp only [mvcc.revOf_sub]
      by_cases h : sint.Z b.Sub' < sint.Z a.Sub'
      · simp only [h, decide_true]; wp_end
      · simp only [h, decide_false]; wp_end

end proof

end EtcdGrove
end Perennial
