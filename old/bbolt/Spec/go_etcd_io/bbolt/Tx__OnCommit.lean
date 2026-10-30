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

/-- `tx.OnCommit(fn)`: appends `fn` to the commit handlers. -/
abbrev Tx.OnCommit.spec : Prop :=
  ∀ (tl : Loc) (t : Tx) (hs : List GoFunc) (fn : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ tl ↦ t ∗ t.commitHandlers' ↦* hs ∗
      ownSliceCap GoFunc t.commitHandlers' (DFrac.own 1) }}
    (App (Val (tl @!! go.GoType.PointerType Tx.ty @!! go!"OnCommit")) (Val #fn))
  {{ (t' : Tx), RET #(); ⌜t' = { t with commitHandlers' := t'.commitHandlers' }⌝ ∗
      tl ↦ t' ∗ t'.commitHandlers' ↦* (hs ++ [fn]) ∗
      ownSliceCap GoFunc t'.commitHandlers' (DFrac.own 1) }}

end spec

end bbolt
end EtcdGrove
end Perennial
