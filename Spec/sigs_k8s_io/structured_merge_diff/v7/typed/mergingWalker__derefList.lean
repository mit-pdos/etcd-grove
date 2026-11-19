/-
`mergingWalker.derefList(prefix, v)` (internal): the list view of a side: nil for an absent side (nil) or
`null`, the view of a list; an error (prefixed) for any other kind. Reads the walker's allocator
field only; the side is lent (any share).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

/-- See the file header. -/
abbrev typed.mergingWalker.derefList.spec : Prop :=
  ∀ (w : Loc) (wv : _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker) (dqw : DFrac) (pfx : GoString) (v : value.Value) (dq : DFrac)
    (o : Option UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ w ↦{dqw} wv ∗ isValO v dq o }}
    (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"derefList")) (Val #pfx)) (Val #v))
  {{ (l : value.List') (errs : GoSlice), RET (PairV #l #errs); w ↦{dqw} wv ∗ isValO v dq o ∗
      isListO l (listOfO o) ∗ errsIff errs (o = none ∨ o = some .null ∨ (listOfO o).isSome) }}

end spec

end smd
end EtcdGrove
end Perennial
