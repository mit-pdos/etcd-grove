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

/-- `tx.ID()`: the transaction id (its meta's `txid`), `-1` for a nil transaction or meta. -/
abbrev Tx.ID.spec : Prop :=
  ∀ (tl : Loc) (t : Tx) (dq : DFrac) (m : internal.common.Meta) (dq2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ (if tl = null then True else
        tl ↦{dq} t ∗ (if t.meta' = null then True else t.meta' ↦{dq2} m)) }}
    (App (Val (tl @!! go.GoType.PointerType Tx.ty @!! go!"ID")) (Val #()))
  {{ RET #(if tl = null then W64 (-1) else if t.meta' = null then W64 (-1) else m.txid');
      (if tl = null then True else
        tl ↦{dq} t ∗ (if t.meta' = null then True else t.meta' ↦{dq2} m)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
