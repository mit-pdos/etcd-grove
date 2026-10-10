/- Lean-first (no Rocq counterpart).

## `node.Propose(ctx, data)` (node.go:469)

A proposal of `data` from any goroutine: `stepWait` of a one-entry `MsgProp`, which `run`
steps as `RawNode.Propose` does. The register application linearizes at application of
the committed entry, so the spec needs no ghost hook: `Propose` returns some error,
having handed the proposal to `run` or not (`ErrProposalDropped` when no leader is
known, ...). Specified for `context.Background()`.
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
abbrev node.Propose.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (data_sl : GoSlice) (data : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      data_sl ↦*□ data }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Propose"))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #data_sl))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
