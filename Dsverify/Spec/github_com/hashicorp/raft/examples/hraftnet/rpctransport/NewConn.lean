/-
`rpctransport.NewConn`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn

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

/-- `NewConn(addr)`: a connection to the net/rpc server at `addr` (no client yet). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.NewConn.spec : Prop :=
  ∀ (W : net.rpc.RpcWorld GF) (a : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        net.rpc.rpcAddr (Gg := hG.goose_globalGS) W a ∗ ⌜receiptBound GF ≤ 2 ^ 64⌝ }}
      (App (Val (@! NewConn)) (Val #a))
    {{ (p : Loc), RET #p; isConn p W a }}

end spec

end Perennial
