/-
`strconv.Atoi` of what `strconv.Itoa` wrote (`strconv.Atoi_dec.spec`), from Perennial's functional
`strconv.Atoi.spec` (its result is `parseInt s 10 0`'s) and its round trip
`internal.strconv.parseInt_fmtInt10_0`. Until 2026-11-28 a hypothesis of `service.Store.Restore`.
-/
module

public import Spec.strconv.Atoi_dec
public import Perennial.Proof.strconv.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.strconv.Assumptions]

theorem strconv.Atoi_dec.wp_proof : _root_.Perennial.strconv.Atoi_dec.spec (GF := GF) (hG := hG) := by
  intro n _
  iintro %Φ #Hpkg HΦ
  have H := _root_.Perennial.strconv.wp_Atoi (GF := GF) (hG := hG)
    (_root_.Perennial.internal.strconv.fmtInt n (W64 10))
  rw [_root_.Perennial.internal.strconv.parseInt_fmtInt10_0] at H
  wp_apply H as %x %err %Hout
  obtain ⟨rfl, rfl⟩ := Hout
  rw [show W64 (sint.Z n) = n by word]
  iapply HΦ
  ipureintro; trivial

end proof

end EtcdGrove
end Perennial
