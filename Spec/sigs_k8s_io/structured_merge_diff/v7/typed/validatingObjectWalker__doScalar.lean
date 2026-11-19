/-
`validatingObjectWalker.doScalar(t)` (internal; the `atomHandler` method for a scalar type): no
error exactly when the value is `null` or a scalar of the kind (`conforms` at a scalar type).

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
abbrev typed.validatingObjectWalker.doScalar.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : VWSt) (dq : DFrac) (x : UVal) (tp : Loc) (s : Scalar),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ vwOwn w sc S st ∗ isValF st.value dq x ∗ tp ↦□ s.goName ∗ ⌜S.find st.t.name = some (.scalar s)⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker.ty @!! go!"doScalar")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; errsIff errs (conforms S st.t x) ∗ isValF st.value dq x ∗
      vwOwn w sc S st }}

end spec

end smd
end EtcdGrove
end Perennial
