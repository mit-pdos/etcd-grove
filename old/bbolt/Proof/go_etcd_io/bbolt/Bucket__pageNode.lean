module
public import Spec.go_etcd_io.bbolt.Bucket__pageNode
public import Spec.go_etcd_io.bbolt.Tx__page

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

theorem Bucket.pageNode.wp_proof (hRoot : InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hpage : Tx.page.spec (GF := GF) (hG := hG)) :
    Bucket.pageNode.spec (GF := GF) (hG := hG) := by
  intro bl bv dqb ib dqi id txl t dqt dbl data ps dq q pg Htx Hnodes Hroot Hinl Hfile
  wp_start as ⟨Hb, Hib, Hres⟩
  wp_auto
  wp_method_call
  try wp_auto
  wp_apply hRoot $$ [Hib] as Hib
  · iframe
  try wp_auto
  wp_if_destruct
  · have Hid0 := Hinl Hif
    subst Hid0
    simp only [Hif, ↓reduceIte]
    try wp_auto
    try rw [Hroot]
    try wp_auto
    iapply HΦ; iframe
  · obtain ⟨Hdb, Hpages, Hc, Hlt, Hlen, Hid, Hfl⟩ := Hfile Hif
    simp only [Hif, ↓reduceIte]
    icases Hres with ⟨Htx, Hd, Hps, Hpg⟩
    try wp_auto
    try rw [Hnodes]
    try wp_auto
    rw [Htx]
    wp_apply hpage txl t dqt dbl data ps dq q id pg Hdb Hpages Hc Hlt Hlen Hid Hfl
      $$ [Htx Hd Hps Hpg] as ⟨Htx, Hd, Hps, Hpg⟩
    · iframe
    try wp_auto
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
