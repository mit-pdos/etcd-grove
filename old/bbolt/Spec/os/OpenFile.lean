module
public import Proof.os.FileModel

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

/-- `os.OpenFile(path, flag, perm)`: on success, an open file holding the file's bytes (none
if it was absent and is created: `O_CREATE`), not mapped. -/
abbrev os.OpenFile.spec : Prop :=
  ∀ (path : GoString) (flag perm : val) (o : Option (List w8)),
  {{ fsFile (GF := GF) path o }}
    (App (App (App (Val #(functions _root_.Perennial.os.OpenFile [])) (Val #path)) (Val flag)) (Val perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
      (⌜err ≠ interface.nil ∧ f = null⌝ ∗ fsFile path o) ∨
      (⌜err = interface.nil ∧ f ≠ null⌝ ∗ ∃ (fd : w64) (bs : List w8),
        ⌜o = some bs ∨ (o = none ∧ bs = [])⌝ ∗ osFile f fd ∗ fileBytes fd bs ∗
        filePath fd path ∗ fileMap fd none) }}

end spec

end bbolt
end EtcdGrove
end Perennial
