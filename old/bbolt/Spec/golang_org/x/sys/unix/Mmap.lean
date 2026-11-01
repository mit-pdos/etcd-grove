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

/-- `unix.Mmap(fd, 0, n, PROT_READ, MAP_SHARED|_)`: on success, the slice `b` of `n` bytes
mapping the file's first `n` bytes, with the caller's half of the cells inside the file. -/
abbrev unix.Mmap.spec : Prop :=
  ∀ (fd : w64) (bs : List w8) (n : w64) (flags : w64),
  0 < sint.Z n → flags &&& W64 1 = W64 1 →
  {{ fileBytes (GF := GF) fd bs ∗ fileMap fd none }}
    (App (App (App (App (App (Val #(functions _root_.Perennial.golang_org.x.sys.unix.Mmap [])) (Val #fd)) (Val #(W64 0))) (Val #n)) (Val #(W64 1))) (Val #flags))
  {{ (b : GoSlice) (err : GoInterface), RET (PairV #b #err);
      fileBytes fd bs ∗
      ((⌜err ≠ interface.nil ∧ ∃ (e : w64), err = interface.mkOk _root_.Perennial.syscall.Errno.ty #e⌝ ∗
        fileMap fd none) ∨
       (⌜err = interface.nil ∧ b.len = n ∧ b.cap = n ∧ b.ptr.locCar ≠ 0⌝ ∗
        fileMap fd (some (b.ptr, sint.nat n)) ∗
        mapRange (some (b.ptr, sint.nat n)) bs 0 (sint.nat n))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
