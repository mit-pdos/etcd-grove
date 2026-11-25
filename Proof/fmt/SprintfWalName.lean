/-
`fmt.Sprintf` of the WAL's segment names, `%016x-%016x.wal`: from Perennial's
`fmt.wp_Sprintf_walName`, over the real `Sprintf` (real `fmt` stage 1, perennial#671; a
trust-boundary axiom from 2026-11-13 until then, when Perennial's model of `Sprintf` left `%0Nx`
arbitrary).
-/
module

public import Spec.fmt.SprintfWalName
public import Perennial.Proof.fmt.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

theorem fmt.SprintfWalName.wp_proof : fmt.SprintfWalName.spec (GF := GF) (hG := hG) := by
  intro s i sl dq
  iintro %Φ Hpre HΦ
  iapply (_root_.Perennial.fmt.wp_Sprintf_walName s i sl dq) $$ Hpre
  inext
  iintro %r ⟨Hsl, %Hr⟩
  iapply HΦ
  iframe
  ipureintro
  rw [Hr, fmt.hexPad16_uint, fmt.hexPad16_uint, fmt.walNameStr]
  simp

end proof

end EtcdGrove
end Perennial
