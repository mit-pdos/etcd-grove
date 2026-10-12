module
public import Proof.go_etcd_io.bbolt.WriteTxLemmas

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

/-- `tx.root.dereference()` of the write transaction at `txl` (what `db.mmap` calls before it
unmaps): every node the buckets' node trees reach gets heap copies of its bytes (`derefRel`),
so that afterwards no byte the transaction keeps is in the view (`noView`, and
`ownWriteTxG_reattach` moves it to the new mapping). The view's pages, which the bytes were
lent from, are given back as they were. -/
abbrev Bucket.dereference.spec : Prop :=
  ∀ (W : WView) (txl : Loc) (T : WTx),
  derefReady T (structFieldRef Tx go!"root" txl) → W.data.locCar ≠ 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWriteTxG W txl T ∗
      pagesView W.data W.ps W.q W.pages }}
    (App (Val (structFieldRef Tx go!"root" txl @!! go.GoType.PointerType Bucket.ty @!! go!"dereference"))
      (Val #()))
  {{ RET #(); ∃ T', ⌜derefRel T T'⌝ ∗ ownWriteTxG W txl T' ∗
      pagesView W.data W.ps W.q W.pages }}

end spec

end bbolt
end EtcdGrove
end Perennial
