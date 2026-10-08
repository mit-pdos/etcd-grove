/-
`newRingBuffer[T](capacity, revisionOf)`. Lean-first (no Rocq counterpart); see
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

/-- `newRingBuffer[T](capacity, revisionOf)`: an empty ring of `capacity` slots, for a
closure `revisionOf` meeting `revisionOfSpec`. Go's code assumes `capacity > 0` ("validated
by Cache"); `capacity ≤ 2^61` keeps `at`'s index arithmetic from overflowing (a ring
that large could not be allocated, but Goose's `make` does not say so). -/
abbrev newRingBuffer.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (capacity : w64) (revisionOf : GoFunc) (isItem : T' → V → IProp GF) (revOf : V → w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ⌜0 < sint.Z capacity ∧ sint.Z capacity ≤ 2 ^ 61⌝ ∗
      revisionOfSpec revisionOf isItem revOf }}
    (App (App (Val #(functions newRingBuffer [T])) (Val #capacity)) (Val #revisionOf))
  {{ (r : Loc), RET #r; ownRingBuffer r (sint.nat capacity) isItem revOf [] }}

end spec

end EtcdGrove
end Perennial
