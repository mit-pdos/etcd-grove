/-
`ringBuffer.moduloIndex` (`cache/ringbuffer.go`), an internal helper: the spec mirrors the code.
Users: the ring buffer's own methods, and no caller in the cache (kept: verified before).
Proof sketch: as the old proof (`specs-ref/Proof/go_etcd_io/etcd/cache/v3/ringBuffer__moduloIndex.lean`), over
`ownRingBuffer`'s realization (`Internal.lean`'s header).
Changes: restated over `Internal.lean`'s opaque `ownRingBuffer` and its transparent pure model (the
same definitions); otherwise unchanged.
Margin: none known.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.cache.v3.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `r.moduloIndex(index)` is `(index + len(r.buffer)) % len(r.buffer)`, i.e. `index`
modulo the buffer's length, for an `index` from `-len` up to where `index + len` would
overflow a Go `int`.

Stated on the struct points-to, not on `ownRingBuffer`: the result depends on nothing
else, and the caller `at` has already loaded `r.buffer` when it calls this, so it needs
the struct back unchanged (an `ownRingBuffer` postcondition would hide which buffer). -/
def ringBuffer.moduloIndex.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T]
    (r : Loc) (rb : ringBuffer T') (dq : DFrac) (index : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ r ↦{dq} rb ∗
      ⌜0 < sint.Z rb.buffer'.len ∧ -sint.Z rb.buffer'.len ≤ sint.Z index ∧
        sint.Z index + sint.Z rb.buffer'.len < 2 ^ 63⌝ }}
    (App (Val (r @!! go.GoType.PointerType (ringBuffer.ty T) @!! go!"moduloIndex"))
      (Val #index))
  {{ RET #(W64 (sint.Z index % sint.Z rb.buffer'.len)); r ↦{dq} rb }}

end spec

end Cache
end EtcdGrove
end Perennial
