/-
`ringBuffer[T].Append(item)`. Lean-first (no Rocq counterpart); see
`InvRingBuffer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvRingBuffer

@[expose] public section

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

/-- `r.Append(item)`, for an `item` modelling `v` whose revision is above the newest
one's (`RevAbove`, which keeps the revisions sorted): `v` is added at the end, and the
oldest item is overwritten if the ring was full (`ringAppend`). `isItem` must be
persistent: the ring keeps `isItem item v` and the caller does too. -/
abbrev ringBuffer.Append.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (revOf : V → w64) (items : List V) (item : T') (v : V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ownRingBuffer r cap isItem revOf items ∗ isItem item v ∗ ⌜RevAbove revOf items v⌝ }}
    (App (Val (r @!! go.GoType.PointerType (ringBuffer.ty T) @!! go!"Append")) (Val #item))
  {{ RET #(); ownRingBuffer r cap isItem revOf (ringAppend cap items v) }}

end spec

end EtcdGrove
end Perennial
