/-
`internal/mem.newSizedBufferPool(size, zero)` (grpc-mem, 2026-11-26): a struct literal, allocated.
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

/-- `newSizedBufferPool(size, zero)` returns a new `*sizedBufferPool` (no ownership is kept: nothing
reads the pools during initialization). -/
abbrev grpc.internal.mem.newSizedBufferPool.spec : Prop :=
  ∀ (size : w64) (zero : bool),
  {{ (True : IProp GF) }}
    (App (App (Val (@! google_golang_org.grpc.internal.mem.newSizedBufferPool)) (Val #size)) (Val #zero))
  {{ (l : Loc), RET #l; True }}

end spec

end EtcdGrove
end Perennial
