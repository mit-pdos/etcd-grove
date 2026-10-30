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

/-- `syscall.Fdatasync(fd)`: no effect (there are no crashes); it may report an error. -/
abbrev syscall.Fdatasync.spec : Prop :=
  ∀ (fd : w64),
  {{ (True : IProp GF) }}
    (App (Val #(functions _root_.Perennial.syscall.Fdatasync [])) (Val #fd))
  {{ (err : GoInterface), RET #err; True }}

end spec

end bbolt
end EtcdGrove
end Perennial
