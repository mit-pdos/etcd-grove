/-
`ringBuffer[T].RemoveLess(rv)`, added by etcd-io/etcd#21676 (not on etcd's main yet). Lean-first
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

/-- The items of `items` whose revision is at least `rv`: what `RemoveLess(rv)` keeps
("drops all entries whose revision is strictly less than rv"). -/
def removeLessItems {V : Type} (revOf : V → w64) (rv : w64) (items : List V) : List V :=
  items.filter (fun v => decide (sint.Z rv ≤ sint.Z (revOf v)))

/-- `r.RemoveLess(rv)`: the items with revision `< rv` are dropped, the others kept in
order; the capacity is unchanged. -/
abbrev ringBuffer.RemoveLess.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF) (revOf : V → w64) (items : List V)
    (rv : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ownRingBuffer r cap isItem revOf items }}
    (App (Val (r @!! go.GoType.PointerType (ringBuffer.ty T) @!! go!"RemoveLess")) (Val #rv))
  {{ RET #(); ownRingBuffer r cap isItem revOf (removeLessItems revOf rv items) }}

end spec

end EtcdGrove
end Perennial
