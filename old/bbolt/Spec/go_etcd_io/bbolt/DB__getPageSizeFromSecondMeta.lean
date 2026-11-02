module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.bbolt.MetaBuf
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Validate
public import Proof.os.FileModel
public import Proof.os.ErrWF
public import Proof.os.FileInfoAlias

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section defs

/-- The buffer `getPageSizeFromSecondMeta` reads at `pos`: up to 4096 bytes of the file, the
rest zero. -/
def probeAt (bs : List w8) (pos : Nat) : List w8 :=
  (bs.drop pos).take 4096 ++ List.replicate (4096 - ((bs.drop pos).take 4096).length) (W8 0)

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
variable [os_fi : OsFileInfoAssumptions (GF := GF)]

/-- `db.getPageSizeFromSecondMeta()`: probes the file at `1024 << i` (`i` up to 14, before its
last KiB) for a valid meta after a page header; the first one found gives the page size.
Otherwise an error. Over the fields it reads. -/
abbrev DB.getPageSizeFromSecondMeta.spec : Prop :=
  ∀ (dbl f : Loc) (fd : w64) (bs : List w8) (ps : w64) (dq : DFrac),
  bs.length < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      structFieldRef DB go!"file" dbl ↦{dq} f ∗ structFieldRef DB go!"pageSize" dbl ↦{dq} ps ∗
      osFile f fd ∗ fileBytes fd bs }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"getPageSizeFromSecondMeta")) (Val #()))
  {{ (sz : w64) (cr : Bool) (err : GoInterface), RET (PairV (PairV #sz #cr) #err);
      structFieldRef DB go!"file" dbl ↦{dq} f ∗ structFieldRef DB go!"pageSize" dbl ↦{dq} ps ∗
      fileBytes fd bs ∗
      ⌜(err = interface.nil ∧ ∃ i < 15, 1024 * 2 ^ i + 1024 < bs.length ∧
          metaValid (metaAt (probeAt bs (1024 * 2 ^ i)) 16) ∧
          sint.Z sz = uint.Z (metaAt (probeAt bs (1024 * 2 ^ i)) 16).pageSize') ∨
        (err ≠ interface.nil ∧ errWF err)⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
