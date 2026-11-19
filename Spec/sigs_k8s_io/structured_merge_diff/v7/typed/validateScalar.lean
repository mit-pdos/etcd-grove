/-
`typed.validateScalar(t, v, prefix)` (internal): no error exactly when the value is absent (nil),
`null`, or a scalar of the kind `t` points to (`scalarOk`). The value is lent (any share).

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
abbrev typed.validateScalar.spec : Prop :=
  ∀ (tp : Loc) (s : Scalar) (v : value.Value) (dq : DFrac) (o : Option UVal) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ tp ↦□ s.goName ∗ isValO v dq o }}
    (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validateScalar)) (Val #tp)) (Val #v)) (Val #pfx))
  {{ (errs : GoSlice), RET #errs; isValO v dq o ∗
      errsIff errs (match o with
        | none => True
        | some x => scalarOk s x = true) }}

end spec

end smd
end EtcdGrove
end Perennial
