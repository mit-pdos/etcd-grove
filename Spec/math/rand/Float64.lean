/-
`rand.Float64()` (Go's `math/rand`, names-only in Perennial): a pseudo-random number in `[0, 1)`.
**A named hypothesis** (outside client-go, no axiom this round; the reflector's `watch` draws its
watch timeout with it; phase 4 of `notes/k8s-daemonset-plan.md`, fifth round): `?` in
`etc/link-lean-first-k8scache.txt`. Stated weakly: some `float64` (its bits).
-/
module

public import Proof.math.rand.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `rand.Float64()`: some `float64`. -/
abbrev rand.Float64.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! _root_.Perennial.math.rand.Float64)) (Val #()))
  {{ (x : w64), RET #x; True }}

end spec

end EtcdGrove
end Perennial
