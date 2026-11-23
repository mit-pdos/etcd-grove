/-
SCRATCH (proph-swiftpaxos; drop before the final head): shows the goal after `wp_auto` of
`client.resolveAccept`'s first statements (the word statements' shape), and checks LinHelp's
encoding lemmas and the claim.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.L2Laws
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.ISpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Claim
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section probe
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [client.Assumptions]

set_option goose.wp.extras true

#check @sp.encE_inj
#check @sp.flatMap_valWs_cons
#check @client.claimGhost.wp_proof

theorem probe_resolveAccept (cl seq : w32) (vsl : GoSlice) (v : List w8) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
        vsl ↦*□ v }}
      (App (App (App (Val (@! client.resolveAccept)) (Val #cl)) (Val #seq)) (Val #vsl))
    {{ RET #(); True }} := by
  wp_start as #Hv
  wp_auto
  done

end probe

end Perennial.github_com.imdea_software.swiftpaxos

end
