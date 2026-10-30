/-
`math.Pow(x, y)`: the trust boundary (Perennial translates `math` names-only for `Pow`, and
specifies no float operation). Lean-first; for client-go's exponential failure rate limiter
(`k8s.io/client-go/util/workqueue`).
-/
module

public import Perennial.Proof.math

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

/-- `math.Pow(x, y)`: some `float64` (floats are opaque bit patterns in the model); it returns
(Go's `Pow` is total: special cases give `±Inf`, `NaN` or `0`, never a panic). -/
abbrev math.Pow.spec : Prop :=
  ∀ (x y : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.math }}
    (App (App (Val (@! _root_.Perennial.math.Pow)) (Val #x)) (Val #y))
  {{ (r : w64), RET #r; True }}

end spec

end EtcdGrove
end Perennial
