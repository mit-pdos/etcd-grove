/-
`ringBuffer[T].at(logicalIndex)`. Lean-first (no Rocq counterpart); see
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

/-- `r.at(i)`, for a logical index `i` in range: the entry of item `i`, whose `revision`
is the item's revision and whose `item` models it. (Go's `at` also accepts indices out
of range, wrapping them; no caller passes one.) -/
abbrev ringBuffer.«at».spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF) (revOf : V → w64) (items : List V)
    (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ownRingBuffer r cap isItem revOf items ∗
      ⌜0 ≤ sint.Z i ∧ sint.Z i < items.length⌝ }}
    (App (Val (r @!! go.GoType.PointerType (ringBuffer.ty T) @!! go!"at")) (Val #i))
  {{ (e : entry T') (v : V), RET #e; ownRingBuffer r cap isItem revOf items ∗
      ⌜items[sint.nat i]? = some v ∧ e.revision' = revOf v⌝ ∗ isItem e.item' v }}

end spec

end EtcdGrove
end Perennial
