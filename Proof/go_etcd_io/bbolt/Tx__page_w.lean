module
public import Spec.go_etcd_io.bbolt.Tx__page_w
public import Spec.go_etcd_io.bbolt.DB__page

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

theorem Tx.page.wp_wproof (hpage : DB.page.spec (GF := GF) (hG := hG))
    (hFastCheck : Page.FastCheck.spec (GF := GF) (hG := hG)) :
    Tx.page.wspec (GF := GF) (hG := hG) := by
  intro txl pmap pm dqm dqt dbl data ps dq dqs id p q pg Hp Hc Hlen Hid Hfl
  wp_start as ⟨Hpf, Hm, Hdbf, Hd, Hps, Hpg⟩
  ihave %Hnn := ownMap_not_nil _ _ _ $$ Hm
  wp_auto
  rw [decide_eq_false Hnn, Bool.not_false]
  try wp_auto
  wp_apply wp_map_lookup2 $$ Hm as Hm
  try wp_auto
  rcases Hp with Hp | ⟨Hp, rfl, Hdc, Hlt⟩
  · rw [Hp]
    simp only [Option.getD_some, Option.isSome_some, decide_true]
    try wp_auto
    icases (page_header_bytes (hG := hG) _ q pg Hlen Hc).1 $$ Hpg with ⟨Hhd, Hrest⟩
    wp_apply hFastCheck _ (pageOf pg) q id Hid Hfl $$ [Hhd] as Hhd
    · iframe
    try wp_auto
    iapply HΦ
    iframe
    iapply (page_header_bytes (hG := hG) _ q pg Hlen Hc).2
    iframe
  · rw [Hp]
    simp only [Option.getD_none, Option.isSome_none, decide_false]
    try wp_auto
    wp_apply hpage dbl data ps dq dqs id Hdc Hlt $$ [Hd Hps] as ⟨Hd, Hps⟩
    · iframe
    try wp_auto
    icases (page_header_bytes (hG := hG) _ q pg Hlen Hc).1 $$ Hpg with ⟨Hhd, Hrest⟩
    wp_apply hFastCheck _ (pageOf pg) q id Hid Hfl $$ [Hhd] as Hhd
    · iframe
    try wp_auto
    iapply HΦ
    iframe
    iapply (page_header_bytes (hG := hG) _ q pg Hlen Hc).2
    iframe

end proof

end bbolt
end EtcdGrove
end Perennial
