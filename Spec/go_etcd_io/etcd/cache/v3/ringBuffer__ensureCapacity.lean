/-
`ringBuffer[T].ensureCapacity(minCapacity)`, added by etcd-io/etcd#21676 (not on etcd's main yet). Lean-first
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

/-- `r.ensureCapacity(minCapacity)`, for `minCapacity ≤ 2^60` (so that the doubling
neither overflows a Go `int` nor exceeds the `2^61` slots `ownRingBuffer` allows): the
items are unchanged and the capacity becomes `cap * 2^k` for the least `k` with
`minCapacity ≤ cap * 2^k` (`k = 0`, nothing changes, if `minCapacity ≤ cap`). `isItem`
must be persistent (as for `Append`): the items are copied into the new buffer. -/
abbrev ringBuffer.ensureCapacity.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (revOf : V → w64) (items : List V) (minCapacity : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ownRingBuffer r cap isItem revOf items ∗ ⌜sint.Z minCapacity ≤ 2 ^ 60⌝ }}
    (App (Val (r @!! go.GoType.PointerType (ringBuffer.ty T) @!! go!"ensureCapacity"))
      (Val #minCapacity))
  {{ (k : Nat), RET #(); ownRingBuffer r (cap * 2 ^ k) isItem revOf items ∗
      ⌜sint.Z minCapacity ≤ ((cap * 2 ^ k : Nat) : Int) ∧
        ∀ j < k, ((cap * 2 ^ j : Nat) : Int) < sint.Z minCapacity⌝ }}

end spec

end EtcdGrove
end Perennial
