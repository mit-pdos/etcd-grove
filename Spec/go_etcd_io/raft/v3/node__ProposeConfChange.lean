/- Lean-first (no Rocq counterpart).

## `node.ProposeConfChange`

The node API's spec. (2026-10-28: moved here from `NodeApiDraft.lean`, where it was drafted over the
API's sealed predicates, now `InvNode.lean`'s; until then this file held the triple over raft's
internals, now the proof's private `node.ProposeConfChange.specRaw`.)
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

/-- **`node.ProposeConfChange(ctx, cc)`**: the same, for the conf change `o` that `cc` holds (given
back): its entry has the type and bytes `MarshalConfChange` gives it, raft choosing the term, and the
committed requested entries grow by its `opsOf`: by the entry, but for an empty `ConfChangeV2` (a
leave, `LogEntry.isEmptyV2`), which is no requested entry. The update never fires if the leader
refuses the change (an empty normal entry commits in its place, `raft.go:1341`), and may not fire
for an empty `ConfChangeV2`. (2026-10-29, stage U5: until then the post was `ops ++ [entry]`, an
empty `ConfChangeV2` a requested entry.) (2026-10-29, S1) The update is wrapped in `□?γ.dup`, as
`node.Propose`'s. (raft-final, 2026-10-29, K5: the stopped answer carries `nodeStopped`, `nodeErrS`; until then
`nodeErr`, which `nodeErrS_nodeErr` gives back.) -/
abbrev node.ProposeConfChange.spec : Prop :=
  ∀ (n : Loc) (γ : Cluster) (N : Namespace) (id : w64) (c : GoInterface) (o : ConfChangeIM) (dq : DFrac)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ N id ∗ nodeCtx ctx cd ∗
      ownConfChangeI c dq (some o) ∗
      □?γ.dup (AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γ ops }> @ ⊤ \ ↑N, ∅
         <{ ∀∀ (t : w64) (bs : List w8), ⌜MarshalsConfChange (some o) bs⌝ ∗
              ownCommittedOps γ (ops ++ opsOf [⟨t, confChangeEntryType (some o), bs⟩]),
            COMM True }>) }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ProposeConfChange"))
      (Val #(interface.ok ctx))) (Val #c))
  {{ (err : GoInterface), RET #err; ownConfChangeI c dq (some o) ∗ nodeErrS n γ N cd err }}

end spec

end EtcdGrove
end Perennial
