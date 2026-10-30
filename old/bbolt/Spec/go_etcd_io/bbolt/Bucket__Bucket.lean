module
public import Proof.go_etcd_io.bbolt.BucketChild

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

/-- `V'` is the view of the nested bucket `nb` of the bucket with the view `V`: of the same
transaction and pages, its root that of the value of the leaf element `nb` (a bucket), and it
has no cache of nested buckets (a read transaction's), as `V` has none. -/
def nestedOK (V V' : BktView) (nb : List w8) : Prop :=
  V'.data = V.data ∧ V'.ps = V.ps ∧ V'.pages = V.pages ∧ V'.hwm = V.hwm ∧ V'.tx = V.tx ∧
  V'.txv = V.txv ∧ V'.bkt.buckets' = map.nil ∧
  ∃ pid p pg i, V.pageAt pid = some (p, pg) ∧ pageFlags pg = leafPageFlag ∧ i < pageCount pg ∧
    leafKey pg i = nb ∧ leafFlags pg i % 2 = bucketLeafFlag ∧
    V'.root = W64 (inBucketRoot (leafValue pg i) : Int)

/-- `b.Bucket(name)` in a read transaction (no cache of nested buckets, `buckets` nil): nil, or
the nested bucket `name` (`nestedOK`), which holds a part of its parent (half of it is left to
the caller, the rest comes back with the child's `bktR`). -/
abbrev Bucket.Bucket.spec : Prop :=
  ∀ (bl : Loc) (V : BktView) (q : Qp) (name : GoSlice) (nb : List w8) (dn : DFrac),
  V.bkt.buckets' = map.nil → V.txv.writable' = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bktR bl V q ∗ txStats V.tx ∗
      name ↦*{dn} nb }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"Bucket")) (Val #name))
  {{ (cl : Loc), RET #cl; txStats V.tx ∗ name ↦*{dn} nb ∗
      ((⌜cl = null⌝ ∗ bktR bl V q) ∨
       (∃ (V' : BktView) (qc : Qp), ⌜nestedOK V V' nb⌝ ∗ bktR bl V q.half ∗ bktR cl V' qc ∗
          (bktR cl V' qc -∗ bktR bl V q.half))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
