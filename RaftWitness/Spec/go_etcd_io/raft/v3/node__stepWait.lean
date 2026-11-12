/- Lean-first (no Rocq counterpart).

## `node.stepWait(ctx, m)` (node.go:502)

`stepWithWaitOption(ctx, m, true)`, for `Propose`'s message. (2026-10-16, stage R7a: any
`nodeCtx ctx cd`, the error `propErr cd err`; `node__stepWithWaitOption.lean`.) (2026-10-16, stage
R5: the message
at `ml`, owned, `msgIn ml 1` of `propMsgM` with the entry `propEntryM data` (D6: its bytes); until
then the Goose value `propMsg esl` with the entries' slice, its capacity and the data slice.)
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev node.stepWait.spec : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (ml : Loc) (data : List w8)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode γ id n ∗
      nodeCtx ctx cd ∗
      msgIn ml (DFrac.own 1) ⟨propMsgM, [propEntryM data], none, [], []⟩ ∗
      propData γ.raft (propEntryM data) ∗ entTk γ.raft (propEntryM data) }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"stepWait"))
      (Val #(interface.ok ctx))) (Val #ml))
  {{ (err : GoInterface), RET #err; propErr cd err }}

end spec

end EtcdGrove
end Perennial
