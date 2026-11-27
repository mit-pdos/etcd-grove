/-
`internal/mem.compactExponents(s)` (grpc-mem, 2026-11-26; the model's loop for `slices.Compact` on a
`[]uint8`, `MODEL:` in `models/grpc/internal/mem/buffer_pool.go`).
-/
module

public import GeneratedProof.google_golang_org.grpc.internal.mem

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `compactExponents(s)` returns a prefix `s'` of `s` whose elements are elements of `s`: what
`newBinaryTiered` needs of `slices.Compact` (the exponents stay in range). -/
abbrev grpc.internal.mem.compactExponents.spec : Prop :=
  ∀ (s : GoSlice) (xs : List w8),
  {{ (s ↦* xs : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.internal.mem.compactExponents)) (Val #s))
  {{ (s' : GoSlice) (ys : List w8), RET #s'; s' ↦* ys ∗ ⌜∀ y ∈ ys, y ∈ xs⌝ }}

end spec

end EtcdGrove
end Perennial
