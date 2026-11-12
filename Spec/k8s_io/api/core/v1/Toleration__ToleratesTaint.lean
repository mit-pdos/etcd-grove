/-
`(*Toleration).ToleratesTaint(logger, taint, enableComparisonOperators)` (`k8s.io/api/core/v1`,
`toleration.go`; names only in the translation): **the trust boundary, a named hypothesis pending
approval**. The code compares the toleration's effect, key, operator and value with the taint's
(for `Lt`/`Gt`, parsing both values as integers, `content.IsDecimalInteger` and
`strconv.ParseInt`, logging through `logger.Error` when one does not parse) and returns; it reads
the two structs and writes nothing the caller owns. The spec says: some `bool`, both kept.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.kubernetes.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace corev1

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.api.core.v1.Assumptions]

/-- See the file header. -/
abbrev Toleration.ToleratesTaint.spec : Prop :=
  ∀ (t : Loc) (dq : DFrac) (tv : k8s_io.api.core.v1.Toleration)
    (logger : github_com.go_logr.logr.Logger) (n : Loc) (dq' : DFrac)
    (nv : k8s_io.api.core.v1.Taint) (en : Bool),
  {{ (t ↦{dq} tv : IProp GF) ∗ n ↦{dq'} nv }}
    (App (App (App (Val (t @!! go.GoType.PointerType k8s_io.api.core.v1.Toleration.ty
      @!! go!"ToleratesTaint")) (Val #logger)) (Val #n)) (Val #en))
  {{ (b : Bool), RET #b; t ↦{dq} tv ∗ n ↦{dq'} nv }}

end spec

end corev1
end EtcdGrove
end Perennial
