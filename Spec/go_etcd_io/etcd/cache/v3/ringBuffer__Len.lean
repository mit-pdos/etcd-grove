/-
`ringBuffer[T].Len()`, added by etcd-io/etcd#21676 (not on etcd's main yet). Lean-first
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

/-- `r.Len()`: the number of items, under any fraction of the ring. -/
abbrev ringBuffer.Len.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF) (revOf : V → w64) (items : List V)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ownRingBuffer r cap isItem revOf items dq }}
    (App (Val (r @!! go.GoType.PointerType (ringBuffer.ty T) @!! go!"Len")) (Val #()))
  {{ RET #(W64 items.length); ownRingBuffer r cap isItem revOf items dq }}

end spec

end EtcdGrove
end Perennial
