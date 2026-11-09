/-
`ringBuffer.AscendGreaterOrEqual` (`cache/ringbuffer.go`), an internal helper: the spec mirrors the code.
Users: `demux.resyncLaggingWatchers` (replaying the history from a lagging watcher's position).
Proof sketch: as the old proof (`specs-ref/Proof/go_etcd_io/etcd/cache/v3/ringBuffer__AscendGreaterOrEqual.lean`), over
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

/-- `r.AscendGreaterOrEqual(pivot, iter)` calls `iter` on the items from the first with
revision `≥ pivot` on, oldest first (`ascendGeVisited`), until it returns `false`. With
`iter` meeting `iterSpec` for an invariant `P` (on the number of items visited) and a
final postcondition `Q`: `Q` if `iter` stopped the iteration, `P` of the number of
visited items if not. -/
def ringBuffer.AscendGreaterOrEqual.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF) (revOf : V → w64) (items : List V)
    (pivot : w64) (iter : GoFunc) (P : Nat → IProp GF) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ownRingBuffer r cap isItem revOf items ∗ P 0 ∗
      iterSpec iter isItem revOf (ascendGeVisited revOf pivot items) P Q }}
    (App (App (Val (r @!! go.GoType.PointerType (ringBuffer.ty T) @!! go!"AscendGreaterOrEqual"))
      (Val #pivot)) (Val #iter))
  {{ RET #(); ownRingBuffer r cap isItem revOf items ∗
      (Q ∨ P (ascendGeVisited revOf pivot items).length) }}

end spec

end Cache
end EtcdGrove
end Perennial
