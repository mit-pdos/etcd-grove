module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.mdelete
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.lookup
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.delItem
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.notFound
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.objOut
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.validateFor
public import Perennial.Proof.context.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem mdelete.wp_proof (wp_lookup : lookup.spec (GF := GF) (hG := hG))
    (wp_delItem : delItem.spec (GF := GF) (hG := hG))
    (wp_notFound : notFound.spec (GF := GF) (hG := hG))
    (wp_objOut : objOut.spec (GF := GF) (hG := hG))
    (wp_validateFor : validateFor.spec (GF := GF) (hG := hG)) :
    mdelete.spec (GF := GF) (hG := hG) := by
  intro x s g
  wp_start as #Hs
  unfold storeOwn
  icases Hs with ⟨#Hk, %Hr⟩
  wp_auto
  wp_apply wp_lookup $$ [$Hk] as %it %ok ⟨-, %Hlk⟩
  obtain ⟨hit, hok⟩ : it = (lookupL g.items x.Key').1 ∧ ok = (lookupL g.items x.Key').2 := by
    rw [← Hlk]; exact ⟨rfl, rfl⟩
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8setcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  cases ok
  · have hn : (lookupL g.items x.Key').2 = false := hok.symm
    (try wp_auto)
    wp_apply wp_notFound
    iapply HΦ
    have : mdeleteL x g = (g, notFoundL g.rv x.Key') := by simp [mdeleteL, hn]
    rw [this, ← Hr]
    iframe Hk
    ipureintro; exact ⟨rfl, rfl⟩
  · have hn : (lookupL g.items x.Key').2 = true := hok.symm
    (try wp_auto)
    wp_apply context.wp_Background
    (try wp_auto)
    wp_apply wp_validateFor as %vf #Hvf
    iunfold validateD at Hvf
    (try wp_auto)
    ihave c : c_ptr ↦ Obj.mk it.obj'.Name' it.obj'.Value' it.obj'.ResourceVersion' $$ [c]
    · iexact c
    cases hr : rejects x.Reject' it.obj'.Value'
    · wp_apply Hvf $$ [$c] as %err Hc Herr
      isimp only [hr, Bool.false_eq_true, ↓reduceIte] at Herr
      icases Herr with %Herr
      subst Herr
      (try wp_auto)
      wp_apply wp_delItem s.items' g.items DFrac.discard x.Key' $$ [$Hk] as %out ⟨-, Hout, -⟩
      ipersist Hout
      (try wp_auto)
      wp_apply wp_objOut
      iapply HΦ
      have : mdeleteL x g = (⟨delItemL g.items x.Key', g.rv + W64 1⟩,
          objOutL ⟨it.obj'.Name', it.obj'.Value', g.rv + W64 1⟩) := by
        simp [mdeleteL, hn, ← hit, hr]
      rw [this, ← Hr]
      iframe Hout
      ipureintro; exact ⟨rfl, rfl⟩
    · wp_apply Hvf $$ [$c] as %err Hc Herr
      isimp only [hr, ↓reduceIte] at Herr
      icases Hi with ⟨-, -, -, -, #EV, -⟩
      ihave %Hne := errVar_ne_nil _ err $$ [$EV $Herr]
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei =>
        (try wp_auto)
        iapply HΦ
        have : mdeleteL x g = (g, rejectedL) := by simp [mdeleteL, hn, ← hit, hr]
        rw [this]
        iframe Hk
        ipureintro; exact ⟨Hr, rfl⟩

end proof

end k8setcd3
end EtcdGrove
end Perennial
