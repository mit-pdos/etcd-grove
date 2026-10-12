/-
`(*time.Ticker).Stop`, of Go's `time` package: the trust boundary, see `Spec/time/NewTicker.lean`.
-/
module

public import Spec.time.NewTicker

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- `t.Stop()` returns (Go 1.23+: no result); the ticker stays a ticker. -/
abbrev time.Ticker.Stop.spec : Prop :=
  ∀ t : Loc,
  {{ time.isTicker (GF := GF) t }}
    (App (Val (t @!! go.GoType.PointerType time.Ticker.ty @!! go!"Stop")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
