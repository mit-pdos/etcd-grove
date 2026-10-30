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

/-- `r.isLeaf()` of a reference to a node or to a page (a writer's cursor). -/
abbrev elemRef.isLeaf.wspec : Prop :=
  ∀ (rl : Loc) (rv : elemRef) (dqr : DFrac) (nv : node) (dqn : DFrac) (q : DFrac) (pg : List w8),
  (rv.node' = null → rv.page'.locCar ≠ 0 ∧ 16 ≤ pg.length) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rl ↦{dqr} rv ∗
      (if rv.node' = null then bytesPointsto rv.page' q pg else rv.node' ↦{dqn} nv) }}
    (App (Val (rl @!! go.GoType.PointerType elemRef.ty @!! go!"isLeaf")) (Val #()))
  {{ RET #(if rv.node' = null then decide (W16 (pageFlags pg) = W16 2) else nv.isLeaf'); rl ↦{dqr} rv ∗
      (if rv.node' = null then bytesPointsto rv.page' q pg else rv.node' ↦{dqn} nv) }}

end spec

end bbolt
end EtcdGrove
end Perennial
