/-
`rpctransport.Transport.deliver`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Trans

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

/-- `t.deliver(cmd, data, hb)`: the `RPC` of `cmd` and `data` with a fresh response channel (whose answers meet `Q`) to server `i`'s consumer or, for a heartbeat (`hb`) once raft set a handler, to that handler on a goroutine of its own; then raft's response. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.deliver.spec : Prop :=
  ∀ (t : Loc) (γ : github_com.hashicorp.raft.gprot.GNames) (snapP : Nat → List w8 → IProp GF) (i : github_com.hashicorp.raft.proto.SID) (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF) (cmd data : GoInterface) (hb : Bool) (Q : github_com.hashicorp.raft.RPCResponse → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ isTrans t γ snapP i W C ∗
        (∀ (ch : Loc) (γc : ChanNames), isChanBag (V := github_com.hashicorp.raft.RPCResponse) γc ch Q -∗
          (github_com.hashicorp.raft.rpcP γ snapP i (github_com.hashicorp.raft.RPC.mk cmd data ch) ∧
           (⌜hb = true⌝ -∗ github_com.hashicorp.raft.hbRpcP γ i (github_com.hashicorp.raft.RPC.mk cmd data ch)))) }}
      (App (App (App (Val (t @!! go.GoType.PointerType Transport.ty @!! go!"deliver")) (Val #cmd)) (Val #data)) (Val #hb))
    {{ (res err : GoInterface), RET (PairV #res #err);
        ∃ r : github_com.hashicorp.raft.RPCResponse, ⌜r.Response' = res ∧ r.Error' = err⌝ ∗ Q r }}

end spec

end Perennial
