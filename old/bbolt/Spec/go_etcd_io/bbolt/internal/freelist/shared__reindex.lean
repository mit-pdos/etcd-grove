module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas

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

/-- `t.reindex()`: the cache becomes exactly the free and pending ids (the free ids and the
pending map obtained back through the interface). -/
abbrev shared.reindex.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (s : Loc) (sv : shared) (σ : FLState) (c : GMap w64 Unit),
  I.FreePageIdsSpec →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ I.hdl s ∗ ownSharedC s sv I.iface σ c ∗ I.own s σ.free }}
    (App (Val (s @!! go.GoType.PointerType shared.ty @!! go!"reindex")) (Val #()))
  {{ (sv' : shared) (c' : GMap w64 Unit), RET #();
      ownSharedC s sv' I.iface σ c' ∗ ⌜cacheOK c' σ⌝ ∗ I.own s σ.free }}

end spec

end bbolt
end EtcdGrove
end Perennial
