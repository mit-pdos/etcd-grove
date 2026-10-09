/-
`ringBuffer[T].PeekLatest(pivot)`. Lean-first (no Rocq counterpart);
see `InvRingBuffer.lean`.
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

/-- `r.PeekLatest()`: the revision of the newest item, `0` if there is none. -/
abbrev ringBuffer.PeekLatest.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF) (revOf : V → w64) (items : List V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ownRingBuffer r cap isItem revOf items }}
    (App (Val (r @!! go.GoType.PointerType (ringBuffer.ty T) @!! go!"PeekLatest")) (Val #()))
  {{ RET #(latestRev revOf items); ownRingBuffer r cap isItem revOf items }}

end spec

end EtcdGrove
end Perennial
