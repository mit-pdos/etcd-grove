/-
`strings.TrimSuffix`, proved over Perennial's translation of Go's (`internal/stringslite.TrimSuffix`).
-/
module

public import Spec.strings.TrimSuffix
public import Perennial.Proof.strings.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.strings.Assumptions]

theorem strings.TrimSuffix.wp_proof : strings.TrimSuffix.spec (GF := GF) (hG := hG) := by
  intro s suf
  iintro %Φ - HΦ
  wp_apply _root_.Perennial.strings.wp_TrimSuffix
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
