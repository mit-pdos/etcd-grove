/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/network/Recv.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension (no change to the proofs).
-/
/-
`TCP.Recv` and `Network.Recv`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.network
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.queue.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.Ghost

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : network.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

theorem network.TCP.Recv.wp_proof : network.TCP.Recv.spec (GF := GF) (hG := hG) := by
  intro tcp γ me
  wp_start as #Htcp
  unfold network.isTCP network.isTCPDef network.tcpCore network.fieldsRO
  icases Htcp with ⟨%ns, %v, %hγ, ⟨⟨#Hip, #Hconns, #Hsrcs, #Hq, #Hmu⟩, #Hroot, #Hlock, #Hreg, #Hqueue⟩, #Hcfg, #Hrd, #Hnv⟩
  wp_auto
  wp_apply queue.Queue.Pop.wp $$ [$Hqueue] as %ev %ok Hev
  iapply HΦ
  cases ok
  · simp only [Bool.false_eq_true, ite_false]; itrivial
  · simp only [ite_true] at *
    unfold network.addrOk
    unfold network.evOk
    icases Hev with ⟨%m, Hev, Hf, #Ha, Hc⟩
    subst hγ
    iexists m
    iframe
    iapply network.def_of_addrOkN tcp ns $$ [$Hroot $Ha]

/-- `n.Recv()` through the `Network` interface, as the code calls it (`MethodResolve` on the
interface value, which resolves to the `*TCP`'s method): as `TCP.Recv`. -/
theorem network.Network.Recv.wp_proof : network.Network.Recv.spec (GF := GF) (hG := hG) := by
  intro n γ
  wp_start_folded as Hn
  unfold network.isNet
  icases Hn with ⟨%tcp, %me, %hn, #Htcp⟩
  subst hn
  wp_pures
  wp_apply network.TCP.Recv.wp_proof tcp γ me $$ [$Htcp] as %ev %ok Hev
  iapply HΦ
  cases ok
  · simp only [Bool.false_eq_true, ite_false]; itrivial
  · simp only [ite_true] at *
    icases Hev with ⟨%m, Hev⟩
    iexists tcp, m
    iframe
    ipureintro; rfl

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
