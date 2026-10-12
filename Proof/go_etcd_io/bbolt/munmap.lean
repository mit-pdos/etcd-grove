module
public import Spec.go_etcd_io.bbolt.munmap
public import Spec.golang_org.x.sys.unix.Munmap

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

theorem munmap.wp_proof (hMunmap : unix.Munmap.spec (GF := GF) (hG := hG)) :
    munmap.spec (GF := GF) (hG := hG) := by
  intro dbl dr dp ds fd bs n
  wp_start as ⟨Hdr, Hdp, Hds, Hf, Hm⟩
  wp_auto
  wp_if_destruct
  · icases Hm with (⟨-, Hm⟩ | ⟨%Hc, -⟩)
    · try simp only [↓reduceIte]
      iapply HΦ; iframe
    · exfalso; exact Hc.1 rfl
  icases Hm with (⟨%Hnil, -⟩ | ⟨%Hc, Hmap, Hrange⟩)
  · exact absurd Hnil Hif
  try wp_auto
  wp_apply hMunmap fd bs dr n Hc.2.1 Hc.2.2 $$ [Hf Hmap Hrange] as ⟨Hf, Hmap⟩
  · iframe
  try wp_auto
  simp only [Hif, ↓reduceIte]
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
