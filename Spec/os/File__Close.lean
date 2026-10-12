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

/-- `f.Close()`: the file goes back to the file system with its bytes (it must not be
mapped). -/
abbrev os.File.Close.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (bs : List w8) (path : GoString) (m : Option (Loc × Nat)),
  {{ osFile (GF := GF) f fd ∗ fileBytes fd bs ∗ filePath fd path ∗ fileMap fd m }}
    (App (Val (f @!! go.GoType.PointerType _root_.Perennial.os.File.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; fsFile path (some bs) }}

end spec

end bbolt
end EtcdGrove
end Perennial
