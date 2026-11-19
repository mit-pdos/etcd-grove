/-
`(*UpdaterBuilder).BuildUpdater()`: an updater with the builder's converter, ignored fields,
ignore filter and `ReturnInputOnNoop`.

Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs

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
variable [package_sem : merge.Assumptions]

/-- See the file header. -/
abbrev merge.UpdaterBuilder.BuildUpdater.spec : Prop :=
  ∀ (b : Loc) (dq : DFrac) (ub : merge.UpdaterBuilder),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗ b ↦{dq} ub }}
    (App (Val (b @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.UpdaterBuilder.ty @!! go!"BuildUpdater")) (Val #()))
  {{ (u : Loc), RET #u; b ↦{dq} ub ∗
      isUpdater u ub.Converter' ub.IgnoredFields' ub.IgnoreFilter' ub.ReturnInputOnNoop' }}

end spec

end smd
end EtcdGrove
end Perennial
