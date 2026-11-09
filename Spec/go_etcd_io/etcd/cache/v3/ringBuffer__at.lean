/-
`ringBuffer.at` (`cache/ringbuffer.go`), an internal helper: the spec mirrors the code.
Users: the ring buffer's own methods, and no caller in the cache (kept: verified before).
Proof sketch: as the old proof (`specs-ref/Proof/go_etcd_io/etcd/cache/v3/ringBuffer__at.lean`), over
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

/-- `r.at(i)`, for a logical index `i` in range: the entry of item `i`, whose `revision`
is the item's revision and whose `item` models it. (Go's `at` also accepts indices out
of range, wrapping them; no caller passes one.) -/
def ringBuffer.«at».spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF) (revOf : V → w64) (items : List V)
    (dq : DFrac)
    (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ownRingBuffer r cap isItem revOf items dq ∗
      ⌜0 ≤ sint.Z i ∧ sint.Z i < items.length⌝ }}
    (App (Val (r @!! go.GoType.PointerType (ringBuffer.ty T) @!! go!"at")) (Val #i))
  {{ (e : entry T') (v : V), RET #e; ownRingBuffer r cap isItem revOf items dq ∗
      ⌜items[sint.nat i]? = some v ∧ e.revision' = revOf v⌝ ∗ isItem e.item' v }}

end spec

end Cache
end EtcdGrove
end Perennial
