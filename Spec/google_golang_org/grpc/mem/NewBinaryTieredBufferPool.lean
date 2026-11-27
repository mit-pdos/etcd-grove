/-
`mem.NewBinaryTieredBufferPool(exps...)` (grpc-mem, 2026-11-26): `internal/mem`'s, as a `BufferPool`;
what `mem`'s `init` calls for its default pool.
-/
module

public import GeneratedProof.google_golang_org.grpc.mem
public import Proof.go_etcd_io.etcd.cache.v3.Base

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

/-- `NewBinaryTieredBufferPool(exps...)` of exponents at most `62` returns a new
`*internal/mem.BinaryTieredBufferPool`, as a `BufferPool`, and no error. -/
abbrev grpc.mem.NewBinaryTieredBufferPool.spec : Prop :=
  ∀ (s : GoSlice) (xs : List w8),
  (∀ x ∈ xs, uint.Z x ≤ 62) → xs.length ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.internal.mem ∗ s ↦* xs }}
    (App (Val (@! google_golang_org.grpc.mem.NewBinaryTieredBufferPool)) (Val #s))
  {{ (l : Loc), RET (PairV
      #(interface.mkOk (go.GoType.PointerType
        google_golang_org.grpc.internal.mem.BinaryTieredBufferPool.ty) #l)
      #(interface.nil : GoInterface)); True }}

end spec

end EtcdGrove
end Perennial
