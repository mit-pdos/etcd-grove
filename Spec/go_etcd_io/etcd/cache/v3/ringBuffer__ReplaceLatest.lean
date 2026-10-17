/-
`ringBuffer[T].ReplaceLatest(item)`, added by etcd-io/etcd#21676 (not on etcd's main yet). Lean-first
(no Rocq counterpart); see `InvRingBuffer.lean`.
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

/-- `r.ReplaceLatest(item)`, for a non-empty ring (Go panics on an empty one) and an
`item` modelling `v` whose revision is above that of the item before the newest
(`RevAbove revOf items.dropLast v`, which keeps the revisions sorted; the PR's doc
comment does not state it): the newest item is replaced by `v`. `isItem` must be
persistent, as for `Append`. -/
abbrev ringBuffer.ReplaceLatest.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (revOf : V → w64) (items : List V) (item : T') (v : V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ownRingBuffer r cap isItem revOf items ∗ isItem item v ∗
      ⌜items ≠ [] ∧ RevAbove revOf items.dropLast v⌝ }}
    (App (Val (r @!! go.GoType.PointerType (ringBuffer.ty T) @!! go!"ReplaceLatest"))
      (Val #item))
  {{ RET #(); ownRingBuffer r cap isItem revOf (items.dropLast ++ [v]) }}

end spec

end EtcdGrove
end Perennial
