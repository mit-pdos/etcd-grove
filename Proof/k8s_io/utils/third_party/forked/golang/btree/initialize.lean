module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.initialize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI Iris.ProofMode k8s_io.utils.third_party.forked.golang.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

theorem initialize.wp_proof : initialize.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply sync.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_apply sort.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hsort⟩
  wp_apply cmp.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hcmp⟩
  iframe Hown
  is_pkg_init_finish

end proof

end btree
end EtcdGrove
end Perennial
