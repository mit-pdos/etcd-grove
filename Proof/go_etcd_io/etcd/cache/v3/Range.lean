/-
Proof of `Spec/Range.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Range

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

set_option linter.unusedSectionVars false

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Range.wp_proof :
    Range.spec (GF := GF) (hG := hG) := by
  intro startSl endSl start end_
  wp_start as ⟨#Hstart, #Hend⟩
  iapply wp_fupd
  wp_auto
  ipersist start
  ipersist «end»
  imodintro
  simp only [recv_eq_func_mk]
  iapply HΦ
  isplitr
  · ipureintro; intro h; cases h
  unfold keyPredSpec
  iintro %sl' %k
  simp only [rangePred]
  wp_start as #Hk
  wp_auto
  wp_apply bytes.wp_Compare sl' startSl DFrac.discard DFrac.discard k start $$ [$Hk $Hstart] as -
  rw [show sint.Z (W64 0) = 0 by decide]
  wp_if_destruct
  · have h1 : ¬ go.GoStringLt k start := (compareResult_ge k start).1 Hif
    wp_apply bytes.wp_Compare sl' endSl DFrac.discard DFrac.discard k end_ $$ [$Hk $Hend] as -
    have h2 : decide (sint.Z (bytes.compareResult k end_) < 0) = decide (go.GoStringLt k end_) := by
      by_cases hlt : go.GoStringLt k end_ <;> simp [compareResult_lt, hlt]
    rw [show sint.Z (W64 0) = 0 by decide, h2]
    simp only [h1, decide_false, Bool.not_false, Bool.true_and]
    wp_end
  · have h1 : go.GoStringLt k start := Classical.byContradiction fun h =>
      Hif ((compareResult_ge k start).2 h)
    simp only [h1, _root_.decide_true, Bool.not_true, Bool.false_and]
    wp_end

end proof

end EtcdGrove
end Perennial
