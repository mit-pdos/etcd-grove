/-
`ringBuffer[T].moduloIndex(index)`. Lean-first (no Rocq counterpart); see
`InvRingBuffer.lean`.
-/
import EtcdGrove.Cache.InvRingBuffer

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `r.moduloIndex(index)` is `(index + len(r.buffer)) % len(r.buffer)`, i.e. `index`
modulo the buffer's length, for an `index` from `-len` up to where `index + len` would
overflow a Go `int`.

Stated on the struct points-to, not on `ownRingBuffer`: the result depends on nothing
else, and the caller `at` has already loaded `r.buffer` when it calls this, so it needs
the struct back unchanged (an `ownRingBuffer` postcondition would hide which buffer). -/
abbrev ringBuffer.moduloIndex.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T]
    (r : Loc) (rb : ringBuffer T') (index : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ r ↦ rb ∗
      ⌜0 < sint.Z rb.buffer'.len ∧ -sint.Z rb.buffer'.len ≤ sint.Z index ∧
        sint.Z index + sint.Z rb.buffer'.len < 2 ^ 63⌝ }}
    (App (Val (r @!! go.GoType.PointerType (ringBuffer.ty T) @!! go!"moduloIndex"))
      (Val #index))
  {{ RET #(W64 (sint.Z index % sint.Z rb.buffer'.len)); r ↦ rb }}

end spec

end EtcdGrove
end Perennial
