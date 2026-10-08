/-
`ringBuffer[T].findLastIndexLessOrEqual(pivot)`. Lean-first (no Rocq counterpart);
see `InvRingBuffer.lean`.
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

/-- `r.findLastIndexLessOrEqual(pivot)`: the binary search returns one less than the
number of items with revision `≤ pivot` (`leCount`), which, the revisions being sorted,
is the index of the last item with revision `≤ pivot`, or `-1` if there is none. -/
abbrev ringBuffer.findLastIndexLessOrEqual.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF) (revOf : V → w64) (items : List V)
    (dq : DFrac)
    (pivot : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ownRingBuffer r cap isItem revOf items dq }}
    (App (Val (r @!! go.GoType.PointerType (ringBuffer.ty T) @!!
      go!"findLastIndexLessOrEqual")) (Val #pivot))
  {{ RET #(W64 ((leCount revOf pivot items : Int) - 1)); ownRingBuffer r cap isItem revOf items dq }}

end spec

end EtcdGrove
end Perennial
