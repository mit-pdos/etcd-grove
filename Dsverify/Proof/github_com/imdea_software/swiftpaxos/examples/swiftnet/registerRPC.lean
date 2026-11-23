/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/registerRPC.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The proof of `Spec/swiftnet/registerRPC.lean`: `registerRPC()` registers the kit's codec with
the net/rpc model and the gob model (over their `SetCodec`'s specs).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.registerRPC
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.encoding.gob.SetCodec

-- PORT: lab imports dropped: Harness.Proof.net.rpc.Codec

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [SwiftNetPkgState GF]
variable [examples.swiftnet.Assumptions]

theorem registerRPC.wp_proof
    (wp_rpc_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG))
    (wp_gob_SetCodec : encoding.gob.SetCodec.spec (GF := GF)) :
    registerRPC.spec (GF := GF) := by
  have e1 : net.rpc.kitFn go!"rpcEncode" = functions examples.swiftnet.rpcEncode [] := rfl
  have e2 : net.rpc.kitFn go!"rpcDecode" = functions examples.swiftnet.rpcDecode [] := rfl
  have e3 : net.rpc.kitFn go!"rpcMethods" = functions examples.swiftnet.rpcMethods [] := rfl
  have e4 : net.rpc.kitFn go!"rpcCall" = functions examples.swiftnet.rpcCall [] := rfl
  have e5 : net.rpc.kitFn go!"rpcName" = functions examples.swiftnet.rpcName [] := rfl
  wp_start
  wp_auto
  ihave %Hc := typedPointsto_not_null _ _ _ $$ «$a0»
  iStructNamed «$a0»
  ipersist Encode; ipersist Decode; ipersist Methods; ipersist Call; ipersist Name
  wp_apply wp_rpc_SetCodec $$ [] as #Hrpc
  · unfold net.rpc.codecFns
    rw [e1, e2, e3, e4, e5]
    isplitr
    · iframe #
    ipureintro; exact Hc
  ihave %Hg := typedPointsto_not_null _ _ _ $$ «$a0»
  iStructNamed «$a0»
  ipersist Encode; ipersist Decode
  wp_apply wp_gob_SetCodec $$ [] as #Hgob
  · isplitr
    · ipureintro; exact Hg
    unfold encoding.gob.codecFns
    rw [e1, e2]
    iframe #
  iapply HΦ
  iframe #

end proof

end Perennial.github_com.imdea_software.swiftpaxos
