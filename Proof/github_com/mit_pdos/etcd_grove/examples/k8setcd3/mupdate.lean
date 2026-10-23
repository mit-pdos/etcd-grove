module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.mupdate
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.lookup
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.setItem
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.notFound
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.objOut
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.updated

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

theorem mupdate.wp_proof (wp_lookup : lookup.spec (GF := GF) (hG := hG))
    (wp_setItem : setItem.spec (GF := GF) (hG := hG))
    (wp_notFound : notFound.spec (GF := GF) (hG := hG))
    (wp_objOut : objOut.spec (GF := GF) (hG := hG))
    (wp_updated : updated.spec (GF := GF) (hG := hG)) :
    mupdate.spec (GF := GF) (hG := hG) := by
  intro x s g
  wp_start as ⟨#Hs, %Hb⟩
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
    have : mupdateL x g = (g, notFoundL g.rv x.Key') := by simp [mupdateL, hn]
    rw [this, ← Hr]
    iframe Hk
    ipureintro; exact ⟨rfl, rfl⟩
  · have hn : (lookupL g.items x.Key').2 = true := hok.symm
    (try wp_auto)
    cases hr : rejects x.Reject' it.obj'.Value'
    · wp_apply wp_updated x cur_ptr (DFrac.own 1) it.obj'.Name' it.obj'.Value' it.obj'.ResourceVersion'
        $$ [$cur] as %q %err ⟨Hcur, Herr⟩
      isimp only [hr, Bool.false_eq_true, ↓reduceIte] at Herr
      icases Herr with ⟨%Herr, Hq⟩
      obtain ⟨rfl, Hqn⟩ := Herr
      (try wp_auto)
      wp_if_destruct
      · have hv := Hif
        (try wp_auto)
        cases hc : it.canon'
        · (try simp only [hc])
          (try wp_auto)
          (try simp only [hc])
          (try wp_auto)
          wp_apply wp_setItem s.items' g.items DFrac.discard
            ⟨x.Key', ⟨it.obj'.Name', (if x.NoOp' = true then it.obj'.Value' else x.Val'), s.rv' + W64 1⟩, true⟩ $$ [$Hk] as %out ⟨-, Hout, -⟩
          · ipureintro; exact Hb
          ipersist Hout
          (try wp_auto)
          wp_apply wp_objOut
          iapply HΦ
          have : mupdateL x g = (⟨setItemL g.items ⟨x.Key', ⟨it.obj'.Name', (if x.NoOp' = true then it.obj'.Value' else x.Val'), g.rv + W64 1⟩, true⟩,
              g.rv + W64 1⟩, objOutL ⟨it.obj'.Name', (if x.NoOp' = true then it.obj'.Value' else x.Val'), g.rv + W64 1⟩) := by
            simp [mupdateL, updatedL, hn, ← hit, hr, hv, hc]
          rw [this, ← Hr]
          iframe Hout
          ipureintro; exact ⟨rfl, rfl⟩
        · (try simp only [hc])
          (try wp_auto)
          (try simp only [hc])
          (try wp_auto)
          wp_apply wp_objOut
          iapply HΦ
          have : mupdateL x g = (g, objOutL it.obj') := by
            simp [mupdateL, updatedL, hn, ← hit, hr, hv, hc]
          rw [this]
          iframe Hk
          ipureintro; exact ⟨Hr, rfl⟩
      · have hv := Hif
        (try wp_auto)
        wp_apply wp_setItem s.items' g.items DFrac.discard
          ⟨x.Key', ⟨it.obj'.Name', (if x.NoOp' = true then it.obj'.Value' else x.Val'), s.rv' + W64 1⟩, true⟩ $$ [$Hk] as %out ⟨-, Hout, -⟩
        · ipureintro; exact Hb
        ipersist Hout
        (try wp_auto)
        wp_apply wp_objOut
        iapply HΦ
        have : mupdateL x g = (⟨setItemL g.items ⟨x.Key', ⟨it.obj'.Name', (if x.NoOp' = true then it.obj'.Value' else x.Val'), g.rv + W64 1⟩, true⟩,
            g.rv + W64 1⟩, objOutL ⟨it.obj'.Name', (if x.NoOp' = true then it.obj'.Value' else x.Val'), g.rv + W64 1⟩) := by
          simp [mupdateL, updatedL, hn, ← hit, hr, hv]
        rw [this, ← Hr]
        iframe Hout
        ipureintro; exact ⟨rfl, rfl⟩
    · wp_apply wp_updated x cur_ptr (DFrac.own 1) it.obj'.Name' it.obj'.Value' it.obj'.ResourceVersion'
        $$ [$cur] as %q %err ⟨Hcur, Herr⟩
      isimp only [hr, ↓reduceIte] at Herr
      icases Hi with ⟨-, -, -, -, -, #EV⟩
      ihave %Hne := errVar_ne_nil _ err $$ [$EV $Herr]
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei =>
        (try wp_auto)
        iapply HΦ
        have : mupdateL x g = (g, rejectedL) := by simp [mupdateL, hn, ← hit, hr]
        rw [this]
        iframe Hk
        ipureintro; exact ⟨Hr, rfl⟩

end proof

end k8setcd3
end EtcdGrove
end Perennial
