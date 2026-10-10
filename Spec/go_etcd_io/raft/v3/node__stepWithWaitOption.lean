/- Lean-first (no Rocq counterpart).

## `node.stepWithWaitOption(ctx, m, wait)` (node.go:508)

A message to `run`: a proposal on `propc`, with a result channel if `wait` (then waits for
the result), anything else on `recvc`. Specified for `context.Background()` (its `Done()`
is `nil`, so the `ctx` cases never fire) and for the two uses `Propose` and `Step` make of
it: `Propose`'s message (`propMsg`, with `wait`), and a message from the network
(`netP`).
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

/-- What `stepWithWaitOption` is called with (see the file header). -/
def stepArg (γ : NodeNames) (id : w64) (m : raftpb.Message) (wait : Bool) : IProp GF :=
  iprop((⌜m.Type' ≠ MsgProp⌝ ∗ netP γ id m) ∨
    (⌜wait = true⌝ ∗ ∃ (data_sl esl : GoSlice) (data : List w8),
      ⌜m = propMsg esl⌝ ∗ esl ↦* [propEntry data_sl] ∗
      ownSliceCap raftpb.Entry esl (DFrac.own 1) ∗ data_sl ↦*□ data))

/-- See the file header. -/
abbrev node.stepWithWaitOption.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (m : raftpb.Message) (wait : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      stepArg γ id m wait }}
    (App (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"stepWithWaitOption"))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #m)) (Val #wait))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
