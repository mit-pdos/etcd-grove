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

/-- `t.EstimatedWritePageSize()`: the size of the freelist page `Write` writes: the header and
the free and pending ids (one more element if there are `0xFFFF` or more, for the count). -/
abbrev shared.EstimatedWritePageSize.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (s : Loc) (σ : FLState), I.FreeCountSpec →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownShared s I.iface σ ∗ I.own s σ.free }}
    (App (Val (s @!! go.GoType.PointerType shared.ty @!! go!"EstimatedWritePageSize")) (Val #()))
  {{ RET #(W64 (16 + 8 * (if 65535 ≤ σ.allIds.length then σ.allIds.length + 1
      else σ.allIds.length : Nat)));
      ownShared s I.iface σ ∗ I.own s σ.free }}

end spec

end bbolt
end EtcdGrove
end Perennial
