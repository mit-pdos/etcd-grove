/-
`ringBuffer.PeekOldest` (`cache/ringbuffer.go`), an internal helper: the spec mirrors the code.
Users: `demux.updateStoreLocked` (the evicted batch's revision, the demux's new `minRev`).
Proof sketch: as the old proof (`specs-ref/Proof/go_etcd_io/etcd/cache/v3/ringBuffer__PeekOldest.lean`), over
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

/-- `r.PeekOldest()`: the revision of the oldest item, `0` if there is none. -/
def ringBuffer.PeekOldest.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF) (revOf : V → w64) (items : List V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ownRingBuffer r cap isItem revOf items }}
    (App (Val (r @!! go.GoType.PointerType (ringBuffer.ty T) @!! go!"PeekOldest")) (Val #()))
  {{ RET #(oldestRev revOf items); ownRingBuffer r cap isItem revOf items }}

end spec

end Cache
end EtcdGrove
end Perennial
