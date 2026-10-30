module
public import Spec.go_etcd_io.bbolt.Bucket__Bucket

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

/-- `tx.Bucket(name)` in a read transaction: the root bucket's `Bucket(name)`
(`Bucket.Bucket.spec`). -/
abbrev Tx.Bucket.spec : Prop :=
  ∀ (txl : Loc) (V : BktView) (q : Qp) (name : GoSlice) (nb : List w8) (dn : DFrac),
  V.bkt.buckets' = map.nil → V.txv.writable' = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      bktR (structFieldRef Tx go!"root" txl) V q ∗ txStats V.tx ∗ name ↦*{dn} nb }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"Bucket")) (Val #name))
  {{ (cl : Loc), RET #cl; txStats V.tx ∗ name ↦*{dn} nb ∗
      ((⌜cl = null⌝ ∗ bktR (structFieldRef Tx go!"root" txl) V q) ∨
       (∃ (V' : BktView) (qc : Qp), ⌜nestedOK V V' nb⌝ ∗
          bktR (structFieldRef Tx go!"root" txl) V q.half ∗ bktR cl V' qc ∗
          (bktR cl V' qc -∗ bktR (structFieldRef Tx go!"root" txl) V q.half))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
