/- Lean-first (no Rocq counterpart).

## `node.ReadIndex(ctx, rctx)` (node.go:608), a linearizable read's request (2026-10-13)

`step` of `pb.Message{Type: MsgReadIndex, Entries: []pb.Entry{{Data: rctx}}}`, from any
goroutine: the request goes onto `recvc` (`netP`), and `run` steps it as
`RawNode.ReadIndex` does. Specified for `context.Background()`. What the client supplies is
as for `RawNode.ReadIndex` (`Spec/RawNode__ReadIndex.lean`): its context's slice recorded
(`isPropData`, `node_read_register`), the request's record `readReq γ c Lc` and one read
credit; a configuration of more than one voter. The answer is a `ReadState` a later
`Ready` hands out (`readyData`), from which the client reads `readOk` of its read
(`node_readState_data`, `readStateOk_readOk`, `readStateOk_prefix`). The error says only
whether the request reached `run`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode
public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev node.ReadIndex.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (rctx : GoSlice) (c : List w8)
    (Lc : List raftpb.Entry),
  1 < GMap.size γ.raft.reCfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      isPropData γ.raft rctx c ∗ readReq γ.raft c Lc ∗ rdCred γ.raft 1 }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ReadIndex"))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #rctx))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
