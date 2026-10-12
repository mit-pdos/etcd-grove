module
public import Spec.go_etcd_io.bbolt.funlock
public import Spec.os.File__Fd
public import Spec.syscall.Flock

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

theorem funlock.wp_proof (hFd : os.File.Fd.spec (GF := GF) (hG := hG))
    (hFlock : syscall.Flock.spec (GF := GF) (hG := hG)) :
    funlock.spec (GF := GF) (hG := hG) := by
  intro dbl f fd dq
  wp_start as ⟨Hf, #Hof⟩
  wp_auto
  wp_apply hFd f fd $$ [Hof]
  · iexact Hof
  try wp_auto
  wp_apply hFlock as %err %Herr
  try wp_auto
  iapply HΦ; iframe; ipureintro; exact Herr

end proof

end bbolt
end EtcdGrove
end Perennial
