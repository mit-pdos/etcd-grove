module
public import Spec.go_etcd_io.bbolt.DB__getPageSizeFromFirstMeta
public import Spec.go_etcd_io.bbolt.DB__getPageSizeFromSecondMeta

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
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
variable [os_fi : OsFileInfoAssumptions (GF := GF)]

/-- `db.getPageSize()`: the page size of the first meta if it is valid; else of a valid meta
the second probe finds (`getPageSizeFromSecondMeta`); else, if either could read its page,
the `pageSize` field (the option's, or the default); else an error. -/
abbrev DB.getPageSize.spec : Prop :=
  ∀ (dbl f : Loc) (fd : w64) (bs : List w8) (ps : w64) (dq : DFrac),
  bs.length < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      structFieldRef DB go!"file" dbl ↦{dq} f ∗ structFieldRef DB go!"pageSize" dbl ↦{dq} ps ∗
      osFile f fd ∗ fileBytes fd bs }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"getPageSize")) (Val #()))
  {{ (sz : w64) (err : GoInterface), RET (PairV #sz #err);
      structFieldRef DB go!"file" dbl ↦{dq} f ∗ structFieldRef DB go!"pageSize" dbl ↦{dq} ps ∗
      fileBytes fd bs ∗
      ⌜(err = interface.nil ∧
          ((4096 ≤ bs.length ∧ metaValid (metaAt bs 16) ∧
              sint.Z sz = uint.Z (metaAt bs 16).pageSize') ∨
           (∃ i < 15, 1024 * 2 ^ i + 1024 < bs.length ∧
              metaValid (metaAt (probeAt bs (1024 * 2 ^ i)) 16) ∧
              sint.Z sz = uint.Z (metaAt (probeAt bs (1024 * 2 ^ i)) 16).pageSize') ∨
           sz = ps)) ∨
        (err ≠ interface.nil ∧ errWF err)⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
