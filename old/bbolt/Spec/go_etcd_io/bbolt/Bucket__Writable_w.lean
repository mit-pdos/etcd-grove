module
public import Proof.go_etcd_io.bbolt.Init

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

/-- `b.Writable()` of a writer's bucket: the transaction's field `writable`. -/
abbrev Bucket.Writable.wspec : Prop :=
  ∀ (bl : Loc) (bv : Bucket) (dqb : DFrac) (w : Bool) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bl ↦{dqb} bv ∗
      structFieldRef Tx go!"writable" bv.tx' ↦{dq} w }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"Writable")) (Val #()))
  {{ RET #w; bl ↦{dqb} bv ∗ structFieldRef Tx go!"writable" bv.tx' ↦{dq} w }}

end spec

end bbolt
end EtcdGrove
end Perennial
