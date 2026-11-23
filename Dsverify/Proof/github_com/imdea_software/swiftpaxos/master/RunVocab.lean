/-
The definitions, specs and lemmas of `Run.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Perennial.Proof.fmt
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Addr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.NetLab
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.RpcHttpHyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.master.Master__Run

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv
  Perennial.fmt

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [log.Assumptions] [net.http.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]

/-- `rpc.Register`'s obligation on the codec's `Receiver` for the master `m` (not nil), once the
codec is registered and the master's persistent facts hold: it returns a `*Receiver` serving
`withErr masterSpec` under the name `"Master"` (`Net/`'s `rcvrIs`). Proved of the kit's rpcgen
codec in `master/Rcvr.lean`. -/
abbrev master.rcvr.spec : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat),
  ⌜m ≠ null⌝ ∗ net.rpc.codecSet net.rpc.RpcCodec.spec ∗ master.isMaster m γc γm N ⊢
    net.rpc.RpcCodec.spec.rcv (interface.mkOk (go.GoType.PointerType master.Master.ty) #m)
      (net.rpc.rcvrIs net.rpc.RpcCodec.spec
        (interface.mkOk (go.GoType.PointerType master.Master.ty) #m)
        (withErr (sp.masterSpec γc γm)) go!"Master" false)

/-- `m.run()` (the goroutine): waits for the replicas, dials them (over HTTP), makes the first
leader, pings them forever. It owns `nodes`' contents and `nextLeader`. -/
abbrev master.Master.run.spec : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat) (W : net.rpc.RpcWorld netDistGF) (nodesS : GoSlice)
    (nl : w64),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master ∗
      master.isMaster m γc γm N ∗ master.fld m go!"nodes" ↦□ nodesS ∗
      nodesS ↦* List.replicate N null ∗ master.fld m go!"nextLeader" ↦ nl ∗
      ([∗list] a ∈ replicaRpcAddrs, rpcHttp W a) ∗
      ⌜(∀ a ∈ replicaRpcAddrs, W.SS a go!"Replica" = some (withErr (sp.replicaRpcSpec γc γm))) ∧
        nl = W64 (-1)⌝ ∗
      net.rpc.codecSet net.rpc.RpcCodec.spec }}
    (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"run")) (Val #()))
  {{ RET #(); False }}

/-- `Run` from `master.createdFull`. -/
abbrev master.Master.Run.specFull : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat) (W : net.rpc.RpcWorld netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master ∗
      master.createdFull m γc γm N (W64 7001) ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.net.rpc ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.net.http ∗
      ⌜threadBound netDistGF ≤ 2 ^ 31⌝ ∗ net.rpc.srvEnv ∗ H.muxOwner [] ∗
      (∃ γs, H.defaultServer γs) ∗ RpcHttpAddr.rpcLisP W go!":7001" (connectReq defaultRPCPath) connectAns ∗
      ([∗list] a ∈ replicaRpcAddrs, rpcHttp W a) ∗ ⌜master.worldOk γc γm W⌝ ∗
      net.rpc.codecSet net.rpc.RpcCodec.spec }}
    (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"Run")) (Val #()))
  {{ RET #(); True }}

end spec

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions] [dlog.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [log.Assumptions] [net.http.Assumptions]
variable [net.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]

end proof

section frozen
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions] [dlog.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [log.Assumptions] [net.http.Assumptions]
variable [net.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]

end frozen

end Perennial.github_com.imdea_software.swiftpaxos
