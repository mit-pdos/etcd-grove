module
public import Spec.go_etcd_io.bbolt.Tx__page
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

theorem Tx.page.wp_proof (hpage : DB.page.spec (GF := GF) (hG := hG))
    (hFastCheck : Page.FastCheck.spec (GF := GF) (hG := hG)) :
    Tx.page.spec (GF := GF) (hG := hG) := by
  intro txl t dqt dbl data ps dq q id pg Hdb Hpages Hc Hlt Hlen Hid Hfl
  subst Hdb
  wp_start as ⟨Htx, Hd, Hps, Hpg⟩
  wp_auto
  rw [Hpages, decide_eq_true rfl, Bool.not_true]
  try wp_auto
  wp_apply hpage t.db' data ps dq id Hc Hlt $$ [Hd Hps] as ⟨Hd, Hps⟩
  · iframe
  try wp_auto
  have Hcar : (data +ₗ uint.Z (id * ps)).locCar ≠ 0 := by simpa [Loc.add] using Hc
  icases (page_header_bytes (hG := hG) _ q pg Hlen Hcar).1 $$ Hpg with ⟨Hhd, Hrest⟩
  wp_apply hFastCheck _ (pageOf pg) q id Hid Hfl $$ [Hhd] as Hhd
  · iframe
  try wp_auto
  iapply HΦ
  iframe
  iapply (page_header_bytes (hG := hG) _ q pg Hlen Hcar).2
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
