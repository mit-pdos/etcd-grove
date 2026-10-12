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

/-- `fi.Size()` of a `FileInfo` from `Stat`: the file's size then. Stated on the call as Goose
emits it (`MethodResolve` on the interface type, whose underlying type is opaque in
Perennial's translation of `io/fs`, so the call cannot be resolved to a method). -/
abbrev fs.FileInfo.Size.spec : Prop :=
  ∀ (fi : GoInterface) (n : Nat),
  {{ fileInfo (GF := GF) fi n }}
    (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.io.fs.FileInfo.ty go!"Size")))
      (Val #fi)) (Val #()))
  {{ RET #(W64 n); True }}

end spec

end bbolt
end EtcdGrove
end Perennial
