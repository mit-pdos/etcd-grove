/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/master/Link.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The master group's results, linked over its proofs. The callees in other groups are taken as
hypotheses, through their specs: `dlog`'s `Printf`/`Fatal` (frozen, `Spec/dlog/`), `defs.NewBeTheLeaderReply` (frozen, `Spec/defs/`) and the kit's
codec functions (`Spec/swiftnet/CodecFns.lean`, change log C7).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.New
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Rcvr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.RunLoop

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions] [dlog.Assumptions]
variable [net.model.Assumptions] [replica.defs.Assumptions]

theorem master.wp_New : master.New.spec := master.New.wp_proof

theorem master.Master.wp_Run
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG))
    (wp_Fatal : dlog.Logger.Fatal.spec (GF := netDistGF) (hG := hG))
    (wp_NBR : replica.defs.NewBeTheLeaderReply.spec)
    (wp_decRA : examples.swiftnet.rpcDecodeAs_defs_RegisterArgs.spec) (wp_decGRL : examples.swiftnet.rpcDecodeAs_defs_GetReplicaListArgs.spec)
    (wp_decGL : examples.swiftnet.rpcDecodeAs_defs_GetLeaderArgs.spec) (wp_put : examples.swiftnet.rpcPutU64.specNil)
    (wp_encRR : examples.swiftnet.rpcEnc_defs_RegisterReply.spec)
    (wp_encGRL : examples.swiftnet.rpcEnc_defs_GetReplicaListReply.spec)
    (wp_encGL : examples.swiftnet.rpcEnc_defs_GetLeaderReply.spec) :
    master.Master.Run.spec :=
  master.Master.Run.wp_proof wp_Printf wp_Fatal (master.Master.run.wp_proof wp_Printf wp_Fatal wp_NBR)
    (master.rcvr.wp_proof wp_Printf wp_decRA wp_decGRL wp_decGL wp_put wp_encRR wp_encGRL wp_encGL)

end link

section linkC
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions] [dlog.Assumptions]
variable [net.model.Assumptions] [replica.defs.Assumptions]
-- the codec (decision D6, Proof/swiftnet/KitLike.lean): `kitCodecC` in the link
variable [C : net.rpc.RpcCodec netDistGF] [KitLike C]

/-- `Run.spec'` (no `kitNameOk`, codec HUB-REQUEST 1), linked as `wp_Run`, over the codec `C`
(codec HUB-REQUEST 2). -/
theorem master.Master.wp_Run'
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG))
    (wp_Fatal : dlog.Logger.Fatal.spec (GF := netDistGF) (hG := hG))
    (wp_NBR : replica.defs.NewBeTheLeaderReply.spec)
    (wp_decRA : examples.swiftnet.rpcDecodeAs_defs_RegisterArgs.spec) (wp_decGRL : examples.swiftnet.rpcDecodeAs_defs_GetReplicaListArgs.spec)
    (wp_decGL : examples.swiftnet.rpcDecodeAs_defs_GetLeaderArgs.spec) (wp_put : examples.swiftnet.rpcPutU64.specNil)
    (wp_encRR : examples.swiftnet.rpcEnc_defs_RegisterReply.spec)
    (wp_encGRL : examples.swiftnet.rpcEnc_defs_GetReplicaListReply.spec)
    (wp_encGL : examples.swiftnet.rpcEnc_defs_GetLeaderReply.spec) :
    master.Master.Run.spec' :=
  master.Master.Run.wp_proof' wp_Printf wp_Fatal (master.Master.run.wp_proof wp_Printf wp_Fatal wp_NBR)
    (master.rcvr.wp_proof wp_Printf wp_decRA wp_decGRL wp_decGL wp_put wp_encRR wp_encGRL wp_encGL)

end linkC

end Perennial.github_com.imdea_software.swiftpaxos
