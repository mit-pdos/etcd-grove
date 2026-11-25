/-
`rand.Float64()` (Go's `math/rand`, names-only in Perennial): a pseudo-random number in `[0, 1)`.
The trust boundary since 2026-11-22 (prove-ps2-rqb: `Proof/math/rand/Float64.lean`, for the client's
`jitterUp`); until then only a named hypothesis (the reflector's `watch` draws its watch timeout
with it; phase 4 of `notes/k8s-daemonset-plan.md`, fifth round: still `?` in
`etc/link-lean-first-k8scache.txt`). Stated weakly: some `float64` (its bits), which is all its
callers need (a float converted to an integer is any integer in Perennial's model).
-/
module

public import Proof.math.rand.Base

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

/-- `rand.Float64()`: some `float64`. (Since math-rand-isinit, 2026-11-24, under `math/rand`'s
`isPkgInit`, Perennial's `isInit`: Go's `Float64` reads the global generator, which `math/rand`'s
initializer sets up.) -/
abbrev rand.Float64.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.math.rand }}
    (App (Val (@! _root_.Perennial.math.rand.Float64)) (Val #()))
  {{ (x : w64), RET #x; True }}

end spec

end EtcdGrove
end Perennial
