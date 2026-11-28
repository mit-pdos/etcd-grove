/-
`hraftnet.serverConns`'s spec (the hraft kit's clients, notes/dsv-hraft.md, S5f).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Addrs
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Base
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
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.Assumptions]
variable [π : Net.NetProtoGS]

open github_com.hashicorp.raft.examples.hraftnet

/-- `serverConns()`: a connection to every server's address (`ServerAddrs()`, index `id - 1`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.serverConns.spec : Prop :=
  ∀ (W : net.rpc.RpcWorld GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
      ([∗list] a ∈ serverAddrs, net.rpc.rpcAddr (Gg := hG.goose_globalGS) W a) ∗
      ⌜receiptBound GF ≤ 2 ^ 64⌝ }}
    (App (Val (@! serverConns)) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ ps : List Loc, sl ↦* ps ∗ ⌜ps.length = 6⌝ ∗
      [∗list] k ↦ p ∈ ps, rpctransport.isConn p W (serverAddrs.getD k go!"") }}

end spec

end Perennial
