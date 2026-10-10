/- Lean-first (no Rocq counterpart).

## `node.stepWait(ctx, m)` (node.go:502)

`stepWithWaitOption(ctx, m, true)`, for `Propose`'s message.
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
variable [AllG GF]

/-- See the file header. -/
abbrev node.stepWait.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (data_sl esl : GoSlice) (data : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      esl ↦* [propEntry data_sl] ∗ ownSliceCap raftpb.Entry esl (DFrac.own 1) ∗
      data_sl ↦*□ data }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"stepWait"))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #(propMsg esl)))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
