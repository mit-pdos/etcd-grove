/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/fieldSel__Matches.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.fieldSel__Matches
public import Spec.k8s_io.apimachinery.pkg.fields.Set__Get

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj labelSel fieldSel)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- `fields.Set.Get` on a read-only set, `nil` included. -/
theorem fields_Get_ro (wp_Get : fields.Set.Get.spec (GF := GF) (hG := hG)) (m : Loc)
    (M : GMap GoString GoString) (k : GoString) (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.fields -∗ mapRO m M -∗
      ▷ Φ #((M !! k).getD []) -∗
      WP (App (Val #(methods k8s_io.apimachinery.pkg.fields.Set'.ty go!"Get" #m)) (Val #k)) {{ Φ }} := by
  iintro #Pf #Hm HΦ
  iunfold mapRO at Hm
  icases Hm with (⟨%hm, %hM⟩ | #Hm)
  · subst hm hM
    wp_method_call
    wp_call
    wp_auto
    simp only [GMap.lookup_empty, Option.getD_none]
    iexact HΦ
  · wp_apply (wp_Get m DFrac.discard M k) $$ [$Hm] as -
    iexact HΦ

set_option hygiene false in
/-- Close a leaf: the answer is `b`. -/
local macro "fsel_close " b:term : tactic => `(tactic| (
  have hb : fmL s M = $b := by
    unfold fmL; simp only [show sint.Z (W64 1) = 1 from rfl, show sint.Z (W64 2) = 2 from rfl] at *; simp_all; (try omega)
  rw [hb]; iapply HΦ; itrivial))

theorem fieldSel.Matches.wp_proof
    (wp_Get : fields.Set.Get.spec (GF := GF) (hG := hG))
    : fieldSel.Matches.spec (GF := GF) (hG := hG) := by
  intro s m M
  wp_start as #Hm
  ihave #Pf : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.fields $$ []
  · iPkgInit
  wp_auto
  wp_if_destruct
  · wp_bind
    iapply (fields_Get_ro wp_Get m M s.f1') $$ Pf Hm
    inext
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_if_destruct
      · wp_bind
        iapply (fields_Get_ro wp_Get m M s.f2') $$ Pf Hm
        inext
        (try wp_auto)
        wp_if_destruct
        · (try wp_auto)
          fsel_close true
        · (try wp_auto)
          fsel_close false
      · (try wp_auto)
        fsel_close true
    · (try wp_auto)
      fsel_close false
  · (try wp_auto)
    wp_if_destruct
    · wp_bind
      iapply (fields_Get_ro wp_Get m M s.f2') $$ Pf Hm
      inext
      (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        fsel_close true
      · (try wp_auto)
        fsel_close false
    · (try wp_auto)
      fsel_close true

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
