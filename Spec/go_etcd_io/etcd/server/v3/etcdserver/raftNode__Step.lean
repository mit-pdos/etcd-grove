/-
`(*raftNode).Step(ctx, m)`: raft's `Node.Step`, promoted. **Users**: `Process` (`server.go:721`).
**Proof sketch**: R1's `node.Step.spec`. **Changes**: unchanged. **Margin**: R1's.
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

def raftNode.Step.spec : Prop :=
  ∀ (r : Loc) (γ : Names) (id : w64) (n : Loc) (ctx : GoInterface) (mp : Loc) (m : Raft.Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isRaftNode r γ id n ∗ Context.ctxOk ctx ∗ Raft.msgPts mp (DFrac.own 1) m ∗
      Raft.msgSent γ.raft m ∗ Raft.msgCredit γ.raft m ∗ ⌜m.to = id⌝ }}
    (App (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.raftNode.ty @!!
      go!"Step")) (Val #ctx)) (Val #mp))
  {{ (err : GoInterface), RET #err; Raft.nodeErr n ctx err }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
