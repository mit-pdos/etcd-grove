/-
`ringBuffer.Append` (`cache/ringbuffer.go`), an internal helper: the spec mirrors the code.
Users: `store.Restore`, `store.applyEventsLocked` (snapshots), `demux.updateStoreLocked` (event batches).
Proof sketch: as the old proof (`specs-ref/Proof/go_etcd_io/etcd/cache/v3/ringBuffer__Append.lean`), over
`ownRingBuffer`'s realization (`Internal.lean`'s header).
Changes: restated over `Internal.lean`'s opaque `ownRingBuffer` and its transparent pure model (the
same definitions); otherwise unchanged.
Margin: none known.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Internal

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

/-- `r.Append(item)`, for an `item` modelling `v` whose revision is above the newest
one's (`RevAbove`, which keeps the revisions sorted): `v` is added at the end, and the
oldest item is overwritten if the ring was full (`ringAppend`). `isItem` must be
persistent: the ring keeps `isItem item v` and the caller does too. -/
def ringBuffer.Append.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (revOf : V → w64) (items : List V) (item : T') (v : V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ownRingBuffer r cap isItem revOf items ∗ isItem item v ∗ ⌜RevAbove revOf items v⌝ }}
    (App (Val (r @!! go.GoType.PointerType (ringBuffer.ty T) @!! go!"Append")) (Val #item))
  {{ RET #(); ownRingBuffer r cap isItem revOf (ringAppend cap items v) }}

end spec

end Cache
end EtcdGrove
end Perennial
