/-
Proof of `Spec/k8s_io/client_go/tools/pager/ListPager__ListWithAlloc.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.pager.ListPager__ListWithAlloc
public import Spec.k8s_io.client_go.tools.pager.ListPager__list

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace pager

open Iris Iris.BI Iris.ProofMode apimodel cache k8s_io.client_go.tools.pager

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.pager.Assumptions]

theorem ListPager.ListWithAlloc.wp_proof (wp_list : ListPager.list.spec (GF := GF) (hG := hG)) :
    ListPager.ListWithAlloc.spec (GF := GF) (hG := hG) := by
  intro p pg opts res S hts hsie
  wp_start as ⟨Hp, #Hpf⟩
  wp_auto
  wp_apply (wp_list p pg opts true res S hts hsie) $$ [$Hp $Hpf] as %obj %pag %err ⟨Hp, Hres⟩
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end pager
end EtcdGrove
end Perennial
