/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/NewBufferClient.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.pkg.TimeInit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NewBufferClient
public import Perennial.Proof.time

-- PORT: lab imports dropped: Harness.Proof.math.rand

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [client.Assumptions] [math.rand.Assumptions] [time.Assumptions]

theorem client.NewBufferClient.wp_proof : client.NewBufferClient.spec (hG := hG) := by
  intro cl cid maddr mport reqNum
  wp_start as ⟨Hfresh, %Hreq⟩
  ihave Hfresh := (client.fresh_unfold _ _ _ _).1 $$ Hfresh
  icases Hfresh with ⟨%v, Hcl, #Hq, %Hv⟩
  ihave %Hnn := typedPointsto_not_null $$ Hcl
  wp_auto
  have hcap : sint.Z (reqNum + W64 1) < 2 ^ 32 := by word
  wp_apply (chan.wp_make2 (V := Loc) (reqNum + W64 1)) as %ch %γch ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; constructor <;> word
  have hne : reqNum + W64 1 ≠ W64 0 := by intro h; have := congrArg sint.Z h; word
  rw [if_neg hne]
  wp_apply (wp_slice_make2 (V := time.Time)) as %rt ⟨Hrt, Hrtc⟩
  · ipureintro; word
  ihave #Htm1 := client.time_init $$ Hpkg
  wp_apply time.wp_Now $$ [$Htm1] as %tm -
  wp_apply time.Time.wp_UnixNano as %x -
  wp_apply math.rand.NewSource.wp_hyp as %src -
  iapply wp_fupd
  wp_apply math.rand.New.wp_hyp as %r ⟨%rv, Hr⟩
  ipersist «$r0»
  imodintro
  iapply HΦ
  iapply (client.bufFresh_unfold _ _ _ _).2
  iexists _, v
  iframe «$r0» Hcl Hq
  isplitr
  · ipureintro
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := Hv
    exact ⟨Hnn, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  iexists γch
  dsimp only
  iframe
  iexact Hch

end proof

end Perennial.github_com.imdea_software.swiftpaxos
