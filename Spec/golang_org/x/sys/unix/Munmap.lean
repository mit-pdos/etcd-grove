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

/-- `unix.Munmap(b)` of the slice `Mmap` returned: the mapping goes, with the caller's half
of its cells. -/
abbrev unix.Munmap.spec : Prop :=
  ∀ (fd : w64) (bs : List w8) (b : GoSlice) (n : Nat),
  b.len = W64 n → b.cap = W64 n →
  {{ fileBytes (GF := GF) fd bs ∗ fileMap fd (some (b.ptr, n)) ∗
      mapRange (some (b.ptr, n)) bs 0 n }}
    (App (Val #(functions _root_.Perennial.golang_org.x.sys.unix.Munmap [])) (Val #b))
  {{ RET #interface.nil; fileBytes fd bs ∗ fileMap fd none }}

end spec

end bbolt
end EtcdGrove
end Perennial
