module
public import Spec.go_etcd_io.bbolt.DB__munmap
public import Spec.go_etcd_io.bbolt.munmap
public import Spec.go_etcd_io.bbolt.DB__invalidate

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

theorem DB.munmap.wp_proof (hmunmap : _root_.Perennial.EtcdGrove.bbolt.munmap.spec (GF := GF) (hG := hG))
    (hinv : DB.invalidate.spec (GF := GF) (hG := hG)) :
    DB.munmap.spec (GF := GF) (hG := hG) := by
  intro dbl d fd bs n
  wp_start as ⟨Hdb, Hf, Hm⟩
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply hmunmap dbl d fd bs n $$ [$Hdb $Hf $Hm] as ⟨Hdb, Hf, Hm⟩
  try wp_auto
  wp_apply hinv $$ [$Hdb] as %d' ⟨%Hd', Hdb⟩
  try wp_auto
  iapply HΦ
  iframe
  ipureintro
  subst Hd'
  split <;> rfl

end proof

end bbolt
end EtcdGrove
end Perennial
