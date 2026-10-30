module
public import Proof.os.FileModel
public import Proof.os.ErrWF

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `f.Stat()`: on success, a `FileInfo` reporting the file's size; an error is a pointer (a
`*PathError`). -/
abbrev os.File.Stat.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (bs : List w8),
  {{ osFile (GF := GF) f fd ∗ fileBytes fd bs }}
    (App (Val (f @!! go.GoType.PointerType _root_.Perennial.os.File.ty @!! go!"Stat")) (Val #()))
  {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err);
      fileBytes fd bs ∗ (⌜err ≠ interface.nil ∧ errWF err⌝ ∨ ⌜err = interface.nil⌝ ∗ fileInfo fi bs.length) }}

end spec

end bbolt
end EtcdGrove
end Perennial
