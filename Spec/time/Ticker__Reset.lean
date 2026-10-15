/-
`(*time.Ticker).Reset`, of Go's `time` package: the trust boundary, see `Spec/time/NewTicker.lean`.
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

/-- `t.Reset(d)` of a positive period returns (no result; Go panics on `d ≤ 0`). -/
abbrev time.Ticker.Reset.spec : Prop :=
  ∀ (t : Loc) (d : time.Duration),
  {{ time.isTicker (GF := GF) t ∗ ⌜0 < sint.Z d⌝ }}
    (App (Val (t @!! go.GoType.PointerType time.Ticker.ty @!! go!"Reset")) (Val #d))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
