module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.bbolt.MetaBuf
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Validate
public import Proof.os.FileModel

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

/-- `db.getPageSizeFromFirstMeta()`: reads the file's first 4096 bytes; if it could (`canRead`)
and the meta in them (after the first page's header) is valid, its page size; otherwise an
error. Over the fields it reads. -/
abbrev DB.getPageSizeFromFirstMeta.spec : Prop :=
  ∀ (dbl f : Loc) (fd : w64) (bs : List w8) (ps : w64) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      structFieldRef DB go!"file" dbl ↦{dq} f ∗ structFieldRef DB go!"pageSize" dbl ↦{dq} ps ∗
      osFile f fd ∗ fileBytes fd bs }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"getPageSizeFromFirstMeta")) (Val #()))
  {{ (sz : w64) (cr : Bool) (err : GoInterface), RET (PairV (PairV #sz #cr) #err);
      structFieldRef DB go!"file" dbl ↦{dq} f ∗ structFieldRef DB go!"pageSize" dbl ↦{dq} ps ∗
      fileBytes fd bs ∗
      ⌜(err = interface.nil ∧ cr = true ∧ 4096 ≤ bs.length ∧ metaValid (metaAt bs 16) ∧
          sint.Z sz = uint.Z (metaAt bs 16).pageSize') ∨
        (err ≠ interface.nil ∧ (cr = true → 4096 ≤ bs.length))⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
