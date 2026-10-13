/-
`(*raftNode).ReadIndex(ctx, rctx)` (raft.go: `raft.Node`'s, promoted through the embedded
`raftNodeConfig`). Lean-first (no Rocq counterpart); the request path's unit 4b (2026-10-13); see
`InvRaftNode.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `r.ReadIndex(ctx, rctx)`: the node's `ReadIndex` (the node contract `isRaftNodeIfc`): with
the big-endian bytes of a request id read-only and a lower bound `n` of the committed index, an
error the gRPC layer can take, and if `nil` the registration `E.RQ id n`. -/
abbrev raftNode.ReadIndex.spec : Prop :=
  ∀ (E : RNEnv GF) (γ : RNNames) (r : Loc) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (sl : GoSlice) (dq : DFrac) (id n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isRaftNode E γ r ∗
      context.isContext ctx cd ∗ sl ↦*{dq} beBytes id ∗ committedAtLeast E.γr n }}
    (App (App (Val (r @!! go.GoType.PointerType raftNode.ty @!! go!"ReadIndex"))
      (Val #(GoInterface.ok ctx))) (Val #sl))
  {{ (err : GoInterface), RET #err; sl ↦*{dq} beBytes id ∗ applyErrIs err ∗
      (⌜err = GoInterface.nil⌝ -∗ □ E.RQ id n) }}

end spec

end EtcdGrove
end Perennial
