/-
`r.ProtoAtLeast(major, minor)` (Go 1.27.3, `request.go`): whether the request's version is at least
`major.minor`; the request is only read (any fraction). Proved in `Net/Proof/net/http/Request__ProtoAtLeast.lean`.
-/
module

public import Net.Proof.net.http.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- See the file header. -/
abbrev Request.ProtoAtLeast.spec : Prop :=
  ∀ (req : Loc) (dq : DFrac) (r : net.http.Request) (major minor : w64),
  {{ (req ↦{dq} r : IProp GF) }}
    (App (App (Val #(methods (go.GoType.PointerType net.http.Request.ty) go!"ProtoAtLeast" #req))
      (Val #major)) (Val #minor))
  {{ RET #(decide (sint.Z major < sint.Z r.ProtoMajor') ||
        decide (r.ProtoMajor' = major) && decide (sint.Z minor ≤ sint.Z r.ProtoMinor')); req ↦{dq} r }}

end spec

end net.http
end Perennial
