module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `t.Copyall(dst)`: the first `Count()` elements of `dst` become the free and pending ids,
sorted. -/
abbrev shared.Copyall.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (s : Loc) (σ : FLState) (dst : GoSlice) (ds : List w64),
  I.FreePageIdsSpec → σ.allIds.length ≤ ds.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownShared s I.iface σ ∗ I.own s σ.free ∗ dst ↦* ds }}
    (App (Val (s @!! go.GoType.PointerType shared.ty @!! go!"Copyall")) (Val #dst))
  {{ (out : List w64), RET #(); ⌜PgidsSorted out ∧ out.Perm σ.allIds⌝ ∗
      dst ↦* (out ++ ds.drop σ.allIds.length) ∗ ownShared s I.iface σ ∗ I.own s σ.free }}

end spec

end bbolt
end EtcdGrove
end Perennial
