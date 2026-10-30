module
public import Spec.go_etcd_io.bbolt.fdatasync
public import Spec.os.File__Fd
public import Spec.syscall.Fdatasync

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem fdatasync.wp_proof (hFd : os.File.Fd.spec (GF := GF) (hG := hG))
    (hSync : syscall.Fdatasync.spec (GF := GF) (hG := hG)) :
    fdatasync.spec (GF := GF) (hG := hG) := by
  intro dbl f fd dq
  wp_start as ⟨Hf, #Hof⟩
  wp_auto
  wp_apply hFd f fd $$ [Hof]
  · iexact Hof
  try wp_auto
  wp_apply hSync as %err -
  try wp_auto
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
