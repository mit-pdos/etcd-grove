module
public import Spec.go_etcd_io.bbolt.DB__Logger

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem DB.Logger.wp_proof (hget : getDiscardLogger.spec (GF := GF) (hG := hG)) :
    DB.Logger.spec (GF := GF) (hG := hG) := by
  intro dbl dq lg dl Hn
  wp_start as ⟨Hlg, #Hdl⟩
  wp_auto
  rw [decide_eq_false Hn]
  try wp_auto
  cases lg with
  | nil =>
    try wp_auto
    wp_apply hget dl $$ [Hdl]
    · iframe; iexact Hdl
    try wp_auto
    simp only [↓reduceIte]
    iapply HΦ; iframe
  | ok i =>
    try wp_auto
    simp only [reduceCtorEq, ↓reduceIte]
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
