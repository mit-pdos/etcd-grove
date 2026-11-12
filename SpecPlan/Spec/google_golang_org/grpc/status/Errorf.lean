/-
`status.Errorf(c, format, args...)` (grpc-go, assumed: `status/status.go`).

Users: `v3rpc.checkRangeStreamRequest` (`key.go:174,177`: constant formats, no arguments).

Why true: `Errorf(c, format)` is `Error(c, fmt.Sprintf(format))`; with no arguments and no `%` in
the format, `Sprintf` returns the format.

Changes: new.

Margin: stated for the call etcd makes (no arguments, no verb).
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `status.Errorf(c, format)` with no arguments, a format without `%`: `status.Error(c, format)`. -/
def Errorf.spec : Prop :=
  ∀ (c : w32) (format : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status ∗ ⌜c ≠ cOK ∧ W8 37 ∉ format⌝ }}
    (App (App (App (Val (@! google_golang_org.grpc.status.Errorf)) (Val #c)) (Val #format)) (Val #slice.nil))
  {{ (err : GoInterface), RET #err; ⌜err ≠ GoInterface.nil⌝ ∗ statusErr err c format }}

end spec

end Grpc
end EtcdGrove
end Perennial
