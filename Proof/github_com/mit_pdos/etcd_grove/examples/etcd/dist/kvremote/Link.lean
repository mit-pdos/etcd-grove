/-
`examples/etcd/dist/kvremote`'s linked results: every proved function's proof applied to its callees'
linked proofs (`enc`'s, `EtcdGrove.enc`; txnlin's `IsWrite`, `Model` and `Gen`, from its proofs: txnlin's
`Link` reaches the whole server; `remote`'s `Run`, `EtcdGrove.remote`).
Hand-written, as `enc`'s (`etc/gen-link.py` has no mode for it).
The Node (`wp_Node`) is linked over `Call_dist_holds` at N2's interim contracts
(`KV_{Put,Get,Delete}_dist`, `Txn_Commit_dist`: axioms until #24's S2 client side).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encCmp
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decCmp
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encTOp
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decTOp
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encVR
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decVR
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encTRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decTRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.encKV
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.decKV
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.EncInput
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.DecInput
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.EncOutput
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.DecOutput
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Codec
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.IsWrite
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Gen
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Model
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.addConfig
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.closure
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpCmp
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpConfig
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpInput
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpInt
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpStore
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpStr
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpTOp
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpVR
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpsOf
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.configEqual
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.delKey
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.genFrom
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.holds
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.inputEqual
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.kvsOf
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.lookup
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.mstep
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.outEqual
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.pick
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.put
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.removeAt
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.resEqual
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.resOf
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.runOps
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.setKey
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.step
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.storeEqual
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.vrEqual
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.withKVs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.withRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.workloadKeys
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Orch
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.isWrite
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.thenOf
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.elseOf
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Node
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.CallDistLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Link
public import Proof.go_uber_org.zap.NewNop
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVPutDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVGetDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVDeleteDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TxnCommitDist

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace EtcdGrove.kvremote

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
open EtcdGrove.enc

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]

theorem wp_IsWrite : EtcdGrove.etcd_txnlin.IsWrite.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.IsWrite.wp_proof (EtcdGrove.etcd_txnlin.isWrite.wp_proof
    EtcdGrove.etcd_txnlin.thenOf.wp_proof EtcdGrove.etcd_txnlin.elseOf.wp_proof)
theorem wp_encCmp : encCmp.spec (GF := GF) (hG := hG) := encCmp.wp_proof Enc.wp_Int Enc.wp_Str Enc.wp_I64
theorem wp_decCmp : decCmp.spec (GF := GF) (hG := hG) := decCmp.wp_proof Dec.wp_Int Dec.wp_Str Dec.wp_I64
theorem wp_encTOp : encTOp.spec (GF := GF) (hG := hG) := encTOp.wp_proof Enc.wp_Int Enc.wp_Str
theorem wp_decTOp : decTOp.spec (GF := GF) (hG := hG) := decTOp.wp_proof Dec.wp_Int Dec.wp_Str
theorem wp_encVR : encVR.spec (GF := GF) (hG := hG) := encVR.wp_proof Enc.wp_Str Enc.wp_I64
theorem wp_decVR : decVR.spec (GF := GF) (hG := hG) := decVR.wp_proof Dec.wp_Str Dec.wp_I64
theorem wp_encTRes : encTRes.spec (GF := GF) (hG := hG) :=
  encTRes.wp_proof Enc.wp_Int Enc.wp_Bool wp_encVR Enc.wp_I64
theorem wp_decTRes : decTRes.spec (GF := GF) (hG := hG) :=
  decTRes.wp_proof Dec.wp_Int Dec.wp_Bool wp_decVR Dec.wp_I64
theorem wp_encKV : encKV.spec (GF := GF) (hG := hG) := encKV.wp_proof Enc.wp_Str wp_encVR
theorem wp_decKV : decKV.spec (GF := GF) (hG := hG) := decKV.wp_proof Dec.wp_Str wp_decVR
theorem wp_EncInput : EncInput.spec (GF := GF) (hG := hG) :=
  EncInput.wp_proof Enc.wp_Int Enc.wp_Str wp_encCmp wp_encTOp
theorem wp_DecInput : DecInput.spec (GF := GF) (hG := hG) :=
  DecInput.wp_proof Dec.wp_Int Dec.wp_Str wp_decCmp wp_decTOp wp_NewDec Dec.wp_Done
theorem wp_EncOutput : EncOutput.spec (GF := GF) (hG := hG) :=
  EncOutput.wp_proof Enc.wp_Bool Enc.wp_I64 wp_encVR Enc.wp_Int wp_encTRes wp_encKV
theorem wp_DecOutput : DecOutput.spec (GF := GF) (hG := hG) :=
  DecOutput.wp_proof Dec.wp_Bool Dec.wp_I64 wp_decVR Dec.wp_Int wp_decTRes wp_decKV wp_NewDec Dec.wp_Done
theorem wp_Codec : Codec.spec (GF := GF) (hG := hG) :=
  Codec.wp_proof wp_EncInput wp_DecInput wp_EncOutput wp_DecOutput wp_IsWrite

/-! txnlin's `Model` and `Gen`, from its proofs (as in txnlin's `Link`). -/
namespace txnlinL

theorem wp_thenOf : EtcdGrove.etcd_txnlin.thenOf.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.thenOf.wp_proof
theorem wp_elseOf : EtcdGrove.etcd_txnlin.elseOf.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.elseOf.wp_proof
theorem wp_isWrite : EtcdGrove.etcd_txnlin.isWrite.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.isWrite.wp_proof wp_thenOf wp_elseOf
theorem wp_lookup : EtcdGrove.etcd_txnlin.lookup.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.lookup.wp_proof
theorem wp_setKey : EtcdGrove.etcd_txnlin.setKey.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.setKey.wp_proof
theorem wp_put : EtcdGrove.etcd_txnlin.put.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.put.wp_proof wp_lookup wp_setKey
theorem wp_delKey : EtcdGrove.etcd_txnlin.delKey.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.delKey.wp_proof
theorem wp_holds : EtcdGrove.etcd_txnlin.holds.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.holds.wp_proof wp_lookup
theorem wp_runOps : EtcdGrove.etcd_txnlin.runOps.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.runOps.wp_proof wp_lookup wp_put wp_delKey
theorem wp_cmpsOf : EtcdGrove.etcd_txnlin.cmpsOf.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.cmpsOf.wp_proof
theorem wp_withRes : EtcdGrove.etcd_txnlin.withRes.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.withRes.wp_proof
theorem wp_withKVs : EtcdGrove.etcd_txnlin.withKVs.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.withKVs.wp_proof
theorem wp_mstep : EtcdGrove.etcd_txnlin.mstep.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.mstep.wp_proof wp_lookup wp_put wp_delKey wp_holds wp_runOps wp_cmpsOf wp_thenOf wp_elseOf wp_withRes wp_withKVs
theorem wp_vrEqual : EtcdGrove.etcd_txnlin.vrEqual.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.vrEqual.wp_proof
theorem wp_resEqual : EtcdGrove.etcd_txnlin.resEqual.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.resEqual.wp_proof wp_vrEqual
theorem wp_kvsOf : EtcdGrove.etcd_txnlin.kvsOf.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.kvsOf.wp_proof
theorem wp_resOf : EtcdGrove.etcd_txnlin.resOf.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.resOf.wp_proof
theorem wp_outEqual : EtcdGrove.etcd_txnlin.outEqual.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.outEqual.wp_proof wp_vrEqual wp_resEqual wp_kvsOf wp_resOf
theorem wp_step : EtcdGrove.etcd_txnlin.step.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.step.wp_proof wp_isWrite wp_mstep wp_outEqual
theorem wp_cmpInt : EtcdGrove.etcd_txnlin.cmpInt.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.cmpInt.wp_proof
theorem wp_cmpStr : EtcdGrove.etcd_txnlin.cmpStr.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.cmpStr.wp_proof
theorem wp_cmpVR : EtcdGrove.etcd_txnlin.cmpVR.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.cmpVR.wp_proof wp_cmpStr wp_cmpInt
theorem wp_cmpStore : EtcdGrove.etcd_txnlin.cmpStore.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.cmpStore.wp_proof wp_cmpInt wp_cmpStr wp_cmpVR
theorem wp_cmpCmp : EtcdGrove.etcd_txnlin.cmpCmp.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.cmpCmp.wp_proof wp_cmpInt wp_cmpStr
theorem wp_cmpTOp : EtcdGrove.etcd_txnlin.cmpTOp.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.cmpTOp.wp_proof wp_cmpInt wp_cmpStr
theorem wp_cmpInput : EtcdGrove.etcd_txnlin.cmpInput.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.cmpInput.wp_proof wp_cmpInt wp_cmpStr wp_cmpCmp wp_cmpTOp
theorem wp_cmpConfig : EtcdGrove.etcd_txnlin.cmpConfig.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.cmpConfig.wp_proof wp_cmpStore wp_cmpInt wp_cmpInput
theorem wp_addConfig : EtcdGrove.etcd_txnlin.addConfig.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.addConfig.wp_proof wp_cmpConfig
theorem wp_removeAt : EtcdGrove.etcd_txnlin.removeAt.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.removeAt.wp_proof
theorem wp_closure : EtcdGrove.etcd_txnlin.closure.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.closure.wp_proof wp_addConfig wp_mstep wp_removeAt
theorem wp_storeEqual : EtcdGrove.etcd_txnlin.storeEqual.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.storeEqual.wp_proof wp_vrEqual
theorem wp_inputEqual : EtcdGrove.etcd_txnlin.inputEqual.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.inputEqual.wp_proof
theorem wp_configEqual : EtcdGrove.etcd_txnlin.configEqual.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.configEqual.wp_proof wp_storeEqual wp_inputEqual
theorem wp_Model : EtcdGrove.etcd_txnlin.Model.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.Model.wp_proof wp_step wp_addConfig wp_closure wp_configEqual
theorem wp_workloadKeys : EtcdGrove.etcd_txnlin.workloadKeys.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.workloadKeys.wp_proof
theorem wp_pick : EtcdGrove.etcd_txnlin.pick.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.pick.wp_proof
theorem wp_genFrom : EtcdGrove.etcd_txnlin.genFrom.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.genFrom.wp_proof wp_workloadKeys wp_pick
theorem wp_Gen : EtcdGrove.etcd_txnlin.Gen.spec (GF := GF) (hG := hG) :=
  EtcdGrove.etcd_txnlin.Gen.wp_proof wp_genFrom

end txnlinL

end linked


section linkedNet
open Net
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable [π : NetProtoGS] [ρ : github_com.mit_pdos.etcd_grove.examples.lib.remote.RemoteGS]
variable [NaInvG GF]

theorem wp_Orch : Orch.spec (GF := GF) (hG := hG) :=
  Orch.wp_proof txnlinL.wp_Model wp_Codec txnlinL.wp_Gen EtcdGrove.remote.wp_Run

end linkedNet

section linkedNode
open Net
open EtcdGrove.etcd_dist
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable [txnlin_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]
variable [etcdstart_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [π : NetProtoGS] [ρ : github_com.mit_pdos.etcd_grove.examples.lib.remote.RemoteGS]
variable [NaInvG GF]

/-- The kv Node, linked: `Call` across machines from `Call_dist_holds` at N2's interim contracts
(`KV_Put_dist`, `KV_Get_dist`, `KV_Delete_dist`, `Txn_Commit_dist`: axioms until #24's S2 client side). -/
theorem wp_Node : Node.spec (GF := GF) (hG := hG) :=
  Node.wp_proof zap.NewNop.wp_proof EtcdGrove.etcdstart.wp_NewClients wp_Codec
    (EtcdGrove.etcd_txnlin.Call_dist_holds KV_Put_dist.wp_proof KV_Get_dist.wp_proof
      KV_Delete_dist.wp_proof Txn_Commit_dist.wp_proof)
    EtcdGrove.remote.wp_ServeClient

end linkedNode

end EtcdGrove.kvremote
end Perennial
