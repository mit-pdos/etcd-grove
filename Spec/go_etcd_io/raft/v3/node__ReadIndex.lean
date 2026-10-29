/- Lean-first (no Rocq counterpart).

## `node.ReadIndex`

The node API's spec. (2026-10-28: moved here from `NodeApiDraft.lean`, where it was drafted over the
API's sealed predicates, now `InvNode.lean`'s; until then this file held the triple over raft's
internals, now the proof's private `node.ReadIndex.specRaw`.)
-/
module

public import Proof.go_etcd_io.raft.v3.InvNode

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

/-- **`node.ReadIndex(ctx, rctx)`**: requests a read with the context `c` (the bytes of `rctx`),
committed to `Q` beforehand (`readCtx_commit`); a `Ready`'s `ReadState` with context `c` then says
what it gave (`readStateOk_ctx`). The context may be retried. (U9, 2026-10-29: raft takes the
request's read credit from a time receipt of its own, `rdPool`; until then the caller's
`readCredit γ`.) -/
abbrev node.ReadIndex.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (rctx : GoSlice) (c : List w8)
    (Q : List LogEntry → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗
      rctx ↦*□ c ∗ isReadCtx γ N c Q }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ReadIndex"))
      (Val #(interface.ok ctx))) (Val #rctx))
  {{ (err : GoInterface), RET #err; nodeErr cd err }}

end spec

end EtcdGrove
end Perennial
