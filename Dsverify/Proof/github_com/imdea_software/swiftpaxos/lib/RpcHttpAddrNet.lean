/-
**`RpcHttpAddr` holds** (notes/dsv-swiftpaxos.md, "Non-vacuity"): the addresses' and listeners'
rpc protocols of `lib/RpcHttpHyps.lean` are Net's (models-rpc-http: `Net/Proof/net/rpc/Proto.lean`'s
`rpcAddrP`, `rpcLisP` and their proved laws), the HTTP world `httpW W` is `W` with HTTP's handshake
at every address, for any package state. The statement `swiftpaxos_remote_robust` instantiates
`RpcHttpAddr` with `netRpcHttpAddr`, so it is no premise; the proofs stay generic in it.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.RpcHttpHyps
public import Net.Proof.net.rpc.Proto

@[expose] public section

noncomputable section

set_option warn.classDefReducibility false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Net Perennial.net.rpc Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **`RpcHttpAddr` from Net's listener protocols** (the file header), for any package state. A
`def`, not an `instance`: the statement gives it to the theorems taking `[RpcHttpAddr GF]`. -/
def netRpcHttpAddr [GoGlobalContext] (GF : BundledGFunctors) [Gg : GooseGlobalGS HasLC.hasLC GF]
    [SwiftNetPkgState GF] : RpcHttpAddr GF where
  rpcAddrP := net.rpc.rpcAddrP (Gg := Gg)
  rpcAddrP_persistent := fun W a hs hsAns => by infer_instance
  worldHs := fun W => W.hs
  worldHsAns := fun W => W.hsAns
  httpW := fun W => { W with hs := fun _ => connectReq defaultRPCPath, hsAns := fun _ => connectAns }
  httpW_hs := fun _ _ => rfl
  httpW_hsAns := fun _ _ => rfl
  httpW_SS := fun _ => rfl
  httpW_reg := fun _ => rfl
  rpcLisP := net.rpc.rpcLisP (Gg := Gg)
  rpcLisP_persistent := fun W la hs hsAns => net.rpc.rpcLisP_persistent W la hs hsAns
  rpcLisP_addr := fun W la hs hsAns a hok hacc => net.rpc.rpcLisP_addr W la hs hsAns a hok hacc
  rpcLisP_lis := fun W la hs hsAns => net.rpc.rpcLisP_lis W la hs hsAns
  rpcLisP_ok := fun W la hs hsAns => net.rpc.rpcLisP_ok W la hs hsAns
  rpcLisP_set := fun E W la hs hsAns hla hhs => net.rpc.rpcLisP_set E W la hs hsAns hla hhs
  rpcAddrP_net := fun _ _ _ _ => .rfl
  rpcLisP_net := fun _ _ _ _ => .rfl
  worldHs_net := fun _ _ => rfl
  worldHsAns_net := fun _ _ => rfl

end Perennial.github_com.imdea_software.swiftpaxos
