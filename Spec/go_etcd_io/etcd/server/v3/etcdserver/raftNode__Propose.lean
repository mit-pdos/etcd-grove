/-
`(*raftNode).Propose(ctx, data)`: raft's `Node.Propose`, promoted through the embedded
`raftNodeConfig` (goose's method wrappers down to the interface field).

**Users**: 2c's `processInternalRaftRequestOnce` (`v3_server.go`: `s.r.Propose(cctx, data)`).
Snippet `raftnode.go` (`ReqPropose`). **Proof sketch**: the field `Node` is `nodeIface n`
(`isRaftNode`); R1's `node.Propose.spec`. **Changes**: unchanged (R1's statement at the driver).
**Margin**: R1's.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false
set_option linter.iris.dupNamespace false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [ctx_sem : context.Assumptions]

def raftNode.Propose.spec : Prop :=
  ∀ (r : Loc) (γ : Names) (id : w64) (n : Loc) (ctx : GoInterface) (data_sl : GoSlice)
    (data : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isRaftNode r γ id n ∗ Context.ctxOk ctx ∗ ownSlice data_sl data DFrac.discard ∗
      (□?γ.raft.dup AU <{ ∃∃ (ops : List Raft.LogEntry), Raft.committedOps γ.raft ops }>
          @ ⊤ \ ↑γ.raft.ns, ∅
        <{ ∀∀ (t : w64), Raft.committedOps γ.raft (ops ++ Raft.opsOf [⟨t, Raft.EntryNormal, data⟩]),
           COMM True }>) }}
    (App (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.raftNode.ty @!!
      go!"Propose")) (Val #ctx)) (Val #data_sl))
  {{ (err : GoInterface), RET #err; Raft.propErr n ctx err }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
