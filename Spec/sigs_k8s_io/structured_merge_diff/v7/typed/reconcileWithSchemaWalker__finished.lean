/-
`reconcileWithSchemaWalker.finished()` (internal): resets the walker (field set, schema, value,
type, path, accumulators) and puts it back in `fmPool` (`rwPooled`: `isAtomic` false, the top
walker's).

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
abbrev typed.reconcileWithSchemaWalker.finished.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : RWSt) (ps : fieldpath.Path) (fs tv rem add sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rwCore w sc S st ps fs tv rem add sp ∗ spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker sp ∗
      ⌜st.isAtomic = false⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker.ty @!! go!"finished")) (Val #()))
  {{ RET #(); True }}

end spec

end smd
end EtcdGrove
end Perennial
