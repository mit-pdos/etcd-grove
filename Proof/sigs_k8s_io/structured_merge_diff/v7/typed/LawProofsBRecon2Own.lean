/-
**`rwOwnAt w sc S st ps F R A sp`**: `rwOwn` (`Walkers.lean`) with the walker's path slice `ps`
named (`rwOwn w sc S st F R A sp ⊣⊢ ∃ ps, rwOwnAt w sc S st ps F R A sp`, by unfolding).

The reconcile cluster's specs (`reconcile`, `doList`, `doMap`, `visitListItems`,
`visitMapItems`, and `doScalar`) take and give back the walker as `rwOwnAt` with the same `ps`
(spec change, Prove phase 2026-11-21, ownership rule: their only callers are the cluster's
bodies and `ReconcileFieldSetWithSchema`): the Go code never reassigns a reconcile walker's
`path` but in `prepareDescent` (the child's), so after `v2.reconcile()` the child's slice is the
one `prepareDescent` gave it, and `prepareDescent`'s wand (`ownPath ps2 _ -∗ ownPath ps _`) gives
the parent's path back. With `rwOwn` (slice hidden) the visitors could not use that wand.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
def rwOwnAt (w sc : Loc) (S : Schema) (st : RWSt) (ps : fieldpath.Path) (F R A : Option PathSet)
    (sp : Loc) : IProp GF :=
  iprop(∃ (fs tv rem add : Loc),
    rwCore w sc S st ps fs tv rem add sp ∗ ownPath ps st.path ∗ isSetO fs F ∗ isSetO rem R ∗
    isSetO add A ∗ spareWalkers typed.reconcileWithSchemaWalker sp)

end own

end smd
end EtcdGrove
end Perennial
