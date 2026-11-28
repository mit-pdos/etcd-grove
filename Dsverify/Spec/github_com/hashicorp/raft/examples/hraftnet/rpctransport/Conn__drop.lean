/-
`rpctransport.Conn.drop`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `p.drop(c)`: forgets `c` if it is still the connection's client, and closes it. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn.drop.spec : Prop :=
  ∀ (p : Loc) (W : net.rpc.RpcWorld GF) (a : GoString) (c : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        isConn p W a ∗ net.rpc.isClient c W a }}
      (App (Val (p @!! go.GoType.PointerType Conn.ty @!! go!"drop")) (Val #c))
    {{ RET #(); True }}

end spec

end Perennial
