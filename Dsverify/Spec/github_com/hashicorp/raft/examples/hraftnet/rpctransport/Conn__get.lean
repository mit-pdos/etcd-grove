/-
`rpctransport.Conn.get`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `p.get(d)`: the connection's client, dialed (`DialTimeout`, `NewClient`) if it has none; `nil` if the dial failed. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn.get.spec : Prop :=
  ∀ (p : Loc) (W : net.rpc.RpcWorld GF) (a : GoString) (d : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        isConn p W a }}
      (App (Val (p @!! go.GoType.PointerType Conn.ty @!! go!"get")) (Val #d))
    {{ (c : Loc), RET #c; ⌜c = null⌝ ∨ net.rpc.isClient c W a }}

end spec

end Perennial
