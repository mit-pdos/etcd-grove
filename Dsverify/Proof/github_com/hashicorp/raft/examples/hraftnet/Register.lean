/-
`hraftnet.Register`'s proof: `SetCodec` of the generated `Codec` (`rpcEncode`, `rpcDecode`,
`rpcReceiver`), which meets `hraftCodec` by definition (`CodecDefs.lean`). As swiftnet's
`RegisterCodec.lean`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.Register
public import Net.Spec.net.rpc.SetCodec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [net.rpc.Assumptions]

set_option goose.wp.extras true

theorem Register.wp_proof (wp_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG)) :
    Register.spec (GF := GF) := by
  wp_start as ⟨#Hmu, Hun⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$a0»
  ipersist «$a0»
  wp_apply wp_SetCodec hraftCodec _ $$ [Hun]
  · isplitr
    · iexact Hmu
    isplitl [Hun]
    · iexact Hun
    isplitr
    · unfold net.rpc.codecIs
      iexists _
      iframe «$a0»
      isplitr
      · iapply hraftCodec_encOk
      isplitr
      · iapply hraftCodec_decOk
      · iapply hraftCodec_rcvOk
    · ipureintro; exact Hnn
  iintro #Hcs
  wp_auto
  iapply HΦ
  iexact Hcs

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
