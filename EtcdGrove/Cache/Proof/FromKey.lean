/-
Proof of `Spec/FromKey.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Cache.Spec.FromKey

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

set_option linter.unusedSectionVars false

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem FromKey.wp_proof :
    FromKey.spec (GF := GF) (hG := hG) := by
  intro sl start
  wp_start as #Hstart
  iapply wp_fupd
  wp_auto
  ipersist start
  imodintro
  simp only [recv_eq_func_mk]
  iapply HΦ
  isplitr
  · ipureintro; intro h; cases h
  unfold keyPredSpec
  iintro %sl' %k
  simp only [fromKeyPred]
  wp_start as #Hk
  wp_auto
  wp_apply bytes.wp_Compare sl' sl DFrac.discard DFrac.discard k start $$ [$Hk $Hstart] as -
  have h : decide (sint.Z (W64 0) ≤ sint.Z (bytes.compareResult k start)) =
      !decide (go.GoStringLt k start) := by
    rw [show sint.Z (W64 0) = 0 by decide]
    by_cases hlt : go.GoStringLt k start <;> simp [compareResult_ge, hlt]
  rw [h]
  wp_end

end proof

end EtcdGrove
end Perennial
