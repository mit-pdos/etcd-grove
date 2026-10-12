module
public import Proof.go_etcd_io.bbolt.BucketRead

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

/-- What `Get(key)` returns: it seeks the leaf (`es`, its top `r` on the leaf page `pg`) where
`key` belongs, at the first element not below `key` (`leafSeekAt`); the value is nil, or that
element's value (a slice into the page), the element's key being `key` and it no bucket. -/
def getOK (V : BktView) (kb : List w8) (v : GoSlice) : Prop :=
  ∃ es r pg, leafTop V es r pg ∧ leafSeekAt pg kb r.index' ∧
    (v = slice.nil ∨ ∃ i : Nat, (i : Int) = sint.Z r.index' ∧ i < pageCount pg ∧
      leafKey pg i = kb ∧ W32 (leafFlags pg i) &&& W32 1 = W32 0 ∧
      v = sliceAt r.page' (elemOff i + leafPos pg i + leafKsize pg i) (leafVsize pg i))

/-- `b.Get(key)` on the read path (see `getOK`). -/
abbrev Bucket.Get.spec : Prop :=
  ∀ (bl : Loc) (V : BktView) (q : Qp) (key : GoSlice) (kb : List w8) (dk : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bktR bl V q ∗ txStats V.tx ∗
      key ↦*{dk} kb }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"Get")) (Val #key))
  {{ (v : GoSlice), RET #v; ⌜getOK V kb v⌝ ∗ bktR bl V q ∗ txStats V.tx ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
