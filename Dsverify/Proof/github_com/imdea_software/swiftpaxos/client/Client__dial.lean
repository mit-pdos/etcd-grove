/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Client__dial.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`c.dial(addr)` (client/client.go): up to three `net.DialTimeout`s.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.ConnectSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Println
public import Perennial.Proof.errors.NewVar

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [client.Assumptions] [net.Assumptions] [net.rpc.Assumptions]
variable [examples.swiftnet.Assumptions] [dlog.Assumptions] [errors.Assumptions] [time.Assumptions]

set_option goose.wp.extras true

theorem client.Client.dial.wp_proof
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG)) :
    client.Client.dial.specI (hG := hG) := by
  intro cl v a P Q
  wp_start as ⟨Hcl, #Hq, #Ha⟩
  wp_auto
  ihave HI : (∃ t : w64, "Htry" ∷ try_ptr ↦ t ∗ "Hcl" ∷ cl ↦ v ∗
      "%Ht" ∷ ⌜0 ≤ sint.Z t ∧ sint.Z t ≤ 3⌝ : IProp netDistGF) $$ [«try» Hcl]
  · iexists _; iframe; ipureintro; word
  wp_for HI
  wp_if_destruct
  · wp_apply net.DialTimeout.labProof a _ P Q $$ [$Ha] as %cv %err Hres
    unfold net.newConnResult
    icases Hres with (⟨%c, %cid, ⟨%Hcv, %Her⟩, Hown, Hend, Hfr⟩ | ⟨%i, %Her, -⟩)
    · subst Hcv Her
      wp_auto
      wp_for_post
      iapply HΦ
      iframe Hcl
      ileft
      iexists c, cid
      iframe
      ipureintro; exact ⟨rfl, rfl⟩
    · subst Her
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨-, -⟩
      wp_auto
      wp_method_call
      wp_call
      wp_auto
      wp_apply wp_Println $$ Hq
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro; word
  · wp_apply errors.wp_New_errorString as %x _
    iapply HΦ
    iframe Hcl
    iright
    ipureintro; simp [interface.mkOk]

end proof

end Perennial.github_com.imdea_software.swiftpaxos
