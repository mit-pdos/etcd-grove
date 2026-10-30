module
public import Spec.go_etcd_io.bbolt.elemRef__isLeaf

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

theorem elemRef.isLeaf.wp_proof (hIsLeafPage : Page.IsLeafPage.spec (GF := GF) (hG := hG)) :
    elemRef.isLeaf.spec (GF := GF) (hG := hG) := by
  intro rl rv dqr q pg Hnode Hc Hlen
  wp_start as ⟨Hr, Hpg⟩
  wp_auto
  rw [Hnode, decide_eq_true rfl, Bool.not_true]
  try wp_auto
  icases (page_header_bytes (hG := hG) _ q pg Hlen Hc).1 $$ Hpg with ⟨Hhd, Hrest⟩
  wp_apply hIsLeafPage _ (pageOf pg) q $$ [Hhd] as Hhd
  · iframe
  try wp_auto
  ihave Hpg := (page_header_bytes (hG := hG) _ q pg Hlen Hc).2 $$ [$Hhd $Hrest]
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
