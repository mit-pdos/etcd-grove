/-
grpc's `codes.Code.String()` (`code_string.go`, translated with its body since status-bodies):
what `(*status.Status).String()` formats with `%s`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.codes.CodeStr
public import Proof.google_golang_org.grpc.codes.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.codes.Assumptions]

/-- `c.String()` returns `codes.codeStr c` (the code's name, or `Code(<decimal>)`). -/
abbrev codes.Code.String.spec : Prop :=
  ∀ (c : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.codes }}
    (App (Val (c @!! google_golang_org.grpc.codes.Code.ty @!! go!"String")) (Val #()))
  {{ RET #(codes.codeStr c); True }}

end spec

end EtcdGrove
end Perennial
