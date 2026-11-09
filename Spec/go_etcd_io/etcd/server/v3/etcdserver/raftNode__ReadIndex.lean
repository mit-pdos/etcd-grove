/-
`(*raftNode).ReadIndex(ctx, rctx)`: raft's `Node.ReadIndex`, promoted. **Users**: 2c's read loop
(`read/read.go`, `readEnv`'s `rf.ReadIndex`). Snippet `raftnode.go` (`ReqReadIndex`).
**Proof sketch**: R1's `node.ReadIndex.spec`. **Changes**: unchanged. **Margin**: R1's.
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

def raftNode.ReadIndex.spec : Prop :=
  ∀ (r : Loc) (γ : Names) (id : w64) (n : Loc) (ctx : GoInterface) (rctx : GoSlice) (c : List w8)
    (Q : List Raft.LogEntry → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isRaftNode r γ id n ∗ Context.ctxOk ctx ∗ ownSlice rctx c DFrac.discard ∗
      Raft.readCtx γ.raft c Q }}
    (App (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.raftNode.ty @!!
      go!"ReadIndex")) (Val #ctx)) (Val #rctx))
  {{ (err : GoInterface), RET #err; Raft.nodeErr n ctx err }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
