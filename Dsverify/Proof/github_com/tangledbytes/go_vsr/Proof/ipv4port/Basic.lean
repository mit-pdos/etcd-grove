/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/ipv4port/Basic.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension.
-/
/-
`FromAddrString`, `String` (value and pointer receivers).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.ipv4port

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : ipv4port.Assumptions]

theorem ipv4port.FromAddrString.wp_proof : ipv4port.FromAddrString.spec (GF := GF) (hG := hG) := fun s => by
  wp_start
  wp_auto
  wp_end

theorem ipv4port.IPv4Port.String.wp_proof : ipv4port.IPv4Port.String.spec (GF := GF) (hG := hG) := fun v => by
  wp_start
  wp_auto
  wp_end

theorem ipv4port.IPv4Port.String_ptr.wp_proof : ipv4port.IPv4Port.String_ptr.spec (GF := GF) (hG := hG) :=
    fun p dq v => by
  wp_start as Hp
  wp_auto
  wp_apply ipv4port.IPv4Port.String.wp_proof
  iapply HΦ $$ Hp

end proofs
end Perennial.github_com.tangledbytes.go_vsr.pkg
