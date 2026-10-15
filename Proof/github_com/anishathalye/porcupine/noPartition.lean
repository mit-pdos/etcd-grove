/- Lean-first (no Rocq counterpart). Proof of `Spec/github_com/anishathalye/porcupine/noPartition.lean`. -/
module

public import Spec.github_com.anishathalye.porcupine.noPartition

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem noPartition.wp_proof : noPartition.spec (GF := GF) (hG := hG) :=
  fun sl ops dq => by
  wp_start as Hs
  wp_auto
  wp_apply wp_slice_literal (V := GoSlice) [sl]
  isplitr
  · ipureintro; rfl
  iintro %r ⟨Hr, -⟩
  wp_auto
  iapply HΦ
  iframe

end proof

end porcupine
end EtcdGrove
end Perennial
