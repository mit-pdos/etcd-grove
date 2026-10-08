/-
`ringBuffer[T].DescendGreaterThan(pivot, iter)`. Lean-first (no Rocq counterpart); see
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

/-- `r.DescendGreaterThan(pivot, iter)` calls `iter` on the items with revision `> pivot`,
newest first (`descendGtVisited`), until it returns `false`. With `iter` meeting
`iterSpec` for an invariant `P` (on the number of items visited) and a final
postcondition `Q`: `Q` if `iter` stopped the iteration, `P` of the number of visited
items if not. -/
abbrev ringBuffer.DescendGreaterThan.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF) (revOf : V → w64) (items : List V)
    (pivot : w64) (iter : GoFunc) (P : Nat → IProp GF) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ownRingBuffer r cap isItem revOf items ∗ P 0 ∗
      iterSpec iter isItem revOf (descendGtVisited revOf pivot items) P Q }}
    (App (App (Val (r @!! go.GoType.PointerType (ringBuffer.ty T) @!! go!"DescendGreaterThan"))
      (Val #pivot)) (Val #iter))
  {{ RET #(); ownRingBuffer r cap isItem revOf items ∗
      (Q ∨ P (descendGtVisited revOf pivot items).length) }}

end spec

end EtcdGrove
end Perennial
