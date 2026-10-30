module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.bbolt.PageView
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage

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

/-- `r.isLeaf()` of a reference to a page (no node, the read path): it is a leaf page, from the page's
bytes. -/
abbrev elemRef.isLeaf.spec : Prop :=
  ∀ (rl : Loc) (rv : elemRef) (dqr : DFrac) (q : DFrac) (pg : List w8),
  rv.node' = null → rv.page'.locCar ≠ 0 → 16 ≤ pg.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rl ↦{dqr} rv ∗ bytesPointsto rv.page' q pg }}
    (App (Val (rl @!! go.GoType.PointerType elemRef.ty @!! go!"isLeaf")) (Val #()))
  {{ RET #(decide (W16 (pageFlags pg) = W16 2)); rl ↦{dqr} rv ∗ bytesPointsto rv.page' q pg }}

end spec

end bbolt
end EtcdGrove
end Perennial
