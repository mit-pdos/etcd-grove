module
public import Proof.go_etcd_io.bbolt.SpillOwn

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

/-- `tx.root.dereference()` (`Bucket.dereference.spec`) during the spill: the nodes are
`nodeOwnX` (`SpillOwn.lean`: a split node has no inodes' capacity), the root node's parent
chain may start outside the tree (`derefReadyX`: those nodes keep no byte of the view, and stay
as they are), and each node keeps its struct but its key (`derefKeep`), so that the capacities
held apart still fit. -/
abbrev Bucket.dereference.xspec : Prop :=
  ∀ (W : WView) (txl : Loc) (T : WTx),
  derefReadyX T (structFieldRef Tx go!"root" txl) → W.data.locCar ≠ 0 →
  (∀ bl B, T.bs !! bl = some B → B.bv.tx' = txl) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      ([∗map] bl ↦ B ∈ T.bs, bktOwnX W bl B) ∗ structFieldRef Tx go!"stats" txl ↦ T.t.stats' ∗
      pagesView W.data W.ps W.q W.pages }}
    (App (Val (structFieldRef Tx go!"root" txl @!! go.GoType.PointerType Bucket.ty @!! go!"dereference"))
      (Val #()))
  {{ RET #(); ∃ T', ⌜derefRelX T T' ∧ derefKeep T T'⌝ ∗ ([∗map] bl ↦ B ∈ T'.bs, bktOwnX W bl B) ∗
      structFieldRef Tx go!"stats" txl ↦ T'.t.stats' ∗ pagesView W.data W.ps W.q W.pages }}

end spec

end bbolt
end EtcdGrove
end Perennial
