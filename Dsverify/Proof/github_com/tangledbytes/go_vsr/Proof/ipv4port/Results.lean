/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/ipv4port/Results.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension.
-/
/-
The results of `ipv4port`: one theorem per spec of `VsrProof/Spec/ipv4port.lean` (stubs at the
freeze: `sorry` until the package's prover proves each).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.ipv4port
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.ipv4port.FromHostPort
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.ipv4port.Basic
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.ipv4port.Sorter

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : ipv4port.Assumptions]

theorem ipv4port.IPv4Port.FromHostPort.wp : ipv4port.IPv4Port.FromHostPort.spec (GF := GF) (hG := hG) := ipv4port.IPv4Port.FromHostPort.wp_proof
theorem ipv4port.FromAddrString.wp : ipv4port.FromAddrString.spec (GF := GF) (hG := hG) := ipv4port.FromAddrString.wp_proof
theorem ipv4port.IPv4Port.String.wp : ipv4port.IPv4Port.String.spec (GF := GF) (hG := hG) := ipv4port.IPv4Port.String.wp_proof
theorem ipv4port.IPv4Port.String_ptr.wp : ipv4port.IPv4Port.String_ptr.spec (GF := GF) (hG := hG) := ipv4port.IPv4Port.String_ptr.wp_proof
theorem ipv4port.ByLess.sorter.wp : ipv4port.ByLess.sorter.spec (GF := GF) (hG := hG) := ipv4port.ByLess.sorter.wp_proof

end results

end Perennial.github_com.tangledbytes.go_vsr.pkg
