module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.bbolt.PageView
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `r.count()` of a reference to a page (no node, the read path): its number of elements, from the page's
bytes. -/
abbrev elemRef.count.spec : Prop :=
  ∀ (rl : Loc) (rv : elemRef) (dqr : DFrac) (q : DFrac) (pg : List w8),
  rv.node' = null → rv.page'.locCar ≠ 0 → 16 ≤ pg.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rl ↦{dqr} rv ∗ bytesPointsto rv.page' q pg }}
    (App (Val (rl @!! go.GoType.PointerType elemRef.ty @!! go!"count")) (Val #()))
  {{ RET #(W64 (pageCount pg)); rl ↦{dqr} rv ∗ bytesPointsto rv.page' q pg }}

end spec

end bbolt
end EtcdGrove
end Perennial
