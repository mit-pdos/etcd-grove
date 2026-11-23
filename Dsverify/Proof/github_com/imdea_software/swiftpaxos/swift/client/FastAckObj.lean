/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/FastAckObj.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`newFastAck()` and `copyFastAck(fa)` (swift/defs.go:344, :357) on the client node, where the
fast-ack pool is off (change log C6: `useFastAckPool ↦□ false` in the handler's context): a
fresh zero `MFastAck`, a fresh copy.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandlerState
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.handler

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions]

abbrev newFastAck.specI : Prop :=
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      globalAddr swift.useFastAckPool ↦□ false }}
    (App (Val (@! swift.newFastAck)) (Val #()))
  {{ (l : Loc), RET #l; l ↦ (zero_val swift.MFastAck) }}

theorem newFastAck.wp_proof : newFastAck.specI (hG := hG) := by
  wp_start as #Hpool
  wp_auto
  iapply HΦ
  iframe

abbrev copyFastAck.specI : Prop :=
  ∀ (l : Loc) (fa : swift.MFastAck),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      globalAddr swift.useFastAckPool ↦□ false ∗ l ↦□ fa }}
    (App (Val (@! swift.copyFastAck)) (Val #l))
  {{ (l' : Loc), RET #l'; l' ↦ fa }}

theorem copyFastAck.wp_proof (wp_new : newFastAck.specI (hG := hG)) :
    copyFastAck.specI (hG := hG) := by
  intro l fa
  wp_start as ⟨#Hpool, #Hl⟩
  ihave #Hf := Hl
  iStructNamed Hf
  wp_auto
  wp_apply wp_new as %l' Hl'
  · iframe #
  iapply HΦ
  iExactEq Hl'
  rfl

end proof

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
