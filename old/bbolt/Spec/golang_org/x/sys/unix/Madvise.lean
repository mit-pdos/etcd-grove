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

/-- `unix.Madvise(b, advice)`: no effect; it may report an error, a `syscall.Errno`. -/
abbrev unix.Madvise.spec : Prop :=
  ∀ (b : GoSlice) (advice : w64),
  {{ (True : IProp GF) }}
    (App (App (Val #(functions _root_.Perennial.golang_org.x.sys.unix.Madvise [])) (Val #b)) (Val #advice))
  {{ (err : GoInterface), RET #err;
      ⌜err = interface.nil ∨ ∃ (e : w64), err = interface.mkOk _root_.Perennial.syscall.Errno.ty #e⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
