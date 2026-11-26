/-
The kit's `Register()` (`rpc_model_gen.go`): from net/rpc's fresh codec state (`codecFresh`, a
boot resource) to `codecSet` of the generated codec (`swiftCodec`, the kit's
`net.rpc.RpcCodec.spec`), over net/rpc's `SetCodec` (dsv-epaxos's `wp_Register`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.NetRpc.Bind

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has netShaExts_hasSha256

namespace cnode

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [log.Assumptions]
  [net.http.Assumptions] [client.Assumptions] [examples.swiftnet.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]

set_option goose.wp.extras true

theorem Register.wp_proof
    (wp_SetCodec : net.rpc.SetCodec.spec (GF := netDistGF) (hG := hG)) :
    Register.spec (hG := hG) := by
  wp_start as Hfr
  iunfold codecFresh at Hfr
  icases Hfr with ⟨#Hmu, Hun⟩
  ihave #Hsync : isPkgInit (PROP := IProp netDistGF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$a0»
  ipersist «$a0»
  wp_apply wp_SetCodec swiftCodec _ $$ [Hun]
  · isplitr
    · iexact Hmu
    isplitl [Hun]
    · iexact Hun
    isplitr
    · unfold net.rpc.codecIs
      iexists _
      iframe «$a0»
      isplitr
      · iapply swiftCodec_encOk
      isplitr
      · iapply swiftCodec_decOk
      · iapply swiftCodec_rcvOk
    · ipureintro; exact Hnn
  iintro #Hcs
  wp_auto
  iapply HΦ
  rw [rpcCodec_spec_eq]
  iexact Hcs

end proof

end cnode

end Perennial.github_com.imdea_software.swiftpaxos
