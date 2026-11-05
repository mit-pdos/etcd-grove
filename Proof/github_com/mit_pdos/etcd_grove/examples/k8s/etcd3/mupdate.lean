module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.sameObj
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.preOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.invalidObj
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.mupdate
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.lookup
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.setItem
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.notFound
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.objOut
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.updated

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- `updated`'s object, field by field (`updated`'s spec). -/
private theorem updatedL_eq (x : Input) (o : Obj) :
    updatedL x o = Obj.mk (if x.NoOp' = true then o.Name' else if o.Name' = [] then x.Key' else o.Name')
      o.UID' (if x.NoOp' = true then o.Value' else x.Val') o.ResourceVersion' := by
  unfold updatedL
  cases x.NoOp' <;> rfl

set_option hygiene false in
/-- `mupdate`'s write: `setItem` of the updated object at the next resource version. -/
local macro "set_tail" : tactic => `(tactic| (
  wp_apply wp_setItem s.items' g.items DFrac.discard _ $$ [Hk] as %out ⟨-, Hout, -⟩
  · iframe Hk; ipureintro; exact Hb
  ipersist Hout
  (try wp_auto)
  wp_apply wp_objOut
  iapply HΦ
  rw [hm, ← Hr]
  iframe Hout
  ipureintro; exact ⟨rfl, rfl⟩))

theorem mupdate.wp_proof (wp_lookup : lookup.spec (GF := GF) (hG := hG))
    (wp_setItem : setItem.spec (GF := GF) (hG := hG))
    (wp_notFound : notFound.spec (GF := GF) (hG := hG))
    (wp_preOk : preOk.spec (GF := GF) (hG := hG))
    (wp_invalidObj : invalidObj.spec (GF := GF) (hG := hG))
    (wp_objOut : objOut.spec (GF := GF) (hG := hG))
    (wp_updated : updated.spec (GF := GF) (hG := hG))
    (wp_sameObj : sameObj.spec (GF := GF) (hG := hG)) :
    mupdate.spec (GF := GF) (hG := hG) := by
  intro x s g
  wp_start as ⟨#Hs, %Hb⟩
  unfold storeOwn
  icases Hs with ⟨#Hk, %Hr⟩
  wp_auto
  wp_apply wp_lookup $$ [$Hk] as %it %ok ⟨-, %Hlk⟩
  obtain ⟨hit, hok⟩ : it = (lookupL g.items x.Key').1 ∧ ok = (lookupL g.items x.Key').2 := by
    rw [← Hlk]; exact ⟨rfl, rfl⟩
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  cases ok
  · have hn : (lookupL g.items x.Key').2 = false := hok.symm
    (try wp_auto)
    cases hi : x.IgnoreNotFound'
    · (try simp only [hi])
      (try wp_auto)
      wp_apply wp_notFound
      iapply HΦ
      have : mupdateL x g = (g, notFoundL g.rv x.Key') := by simp [mupdateL, hn, hi]
      rw [this, ← Hr]
      iframe Hk
      ipureintro; exact ⟨rfl, rfl⟩
    (try simp only [hi])
    (try wp_auto)
    rw [show (zero_val Obj) = Obj.mk [] [] [] (W64 0) from rfl]
    wp_apply wp_preOk
    cases hp : preOkL x (Obj.mk [] [] [] (W64 0))
    · (try wp_auto)
      wp_apply wp_invalidObj
      iapply HΦ
      have : mupdateL x g = (g, invalidObjL x.Key') := by
        simp only [mupdateL, hn, hi, hp, zObj, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte, eq_self_iff_true,
          if_true, _root_.false_and, Bool.and_true, Bool.and_false, Bool.true_eq_false]
      rw [this]
      iframe Hk
      ipureintro; exact ⟨Hr, rfl⟩
    (try wp_auto)
    wp_apply wp_updated x cur_ptr (DFrac.own 1) [] [] [] (W64 0) $$ [$cur] as %q %err ⟨Hcur, Herr⟩
    cases hr : rejects x.Reject' []
    · isimp only [hr, Bool.false_eq_true, ↓reduceIte] at Herr
      icases Herr with ⟨%Herr, Hq⟩
      obtain ⟨rfl, Hqn⟩ := Herr
      (try wp_auto)
      have hm : mupdateL x g = (⟨setItemL g.items ⟨x.Key', Obj.mk
          (if x.NoOp' = true then [] else x.Key')
          [] (if x.NoOp' = true then [] else x.Val') (g.rv + W64 1), true⟩,
          g.rv + W64 1⟩, objOutL (Obj.mk
          (if x.NoOp' = true then [] else x.Key')
          [] (if x.NoOp' = true then [] else x.Val') (g.rv + W64 1))) := by
        simp only [mupdateL, updatedL_eq, hn, hi, zObj, hp, hr, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte, eq_self_iff_true,
          if_true, _root_.false_and, Bool.and_true, Bool.and_false, Bool.true_eq_false]
      set_tail
    · isimp only [hr, ↓reduceIte, if_true] at Herr
      icases Hi with ⟨-, -, -, -, -, #EV⟩
      ihave %Hne := errVar_ne_nil _ err $$ [$EV $Herr]
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei =>
        (try wp_auto)
        iapply HΦ
        have : mupdateL x g = (g, rejectedL) := by
          simp only [mupdateL, hn, hi, zObj, hp, hr, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte, eq_self_iff_true,
          if_true, _root_.false_and, Bool.and_true, Bool.and_false, Bool.true_eq_false]
        rw [this]
        iframe Hk
        ipureintro; exact ⟨Hr, rfl⟩
  · have hn : (lookupL g.items x.Key').2 = true := hok.symm
    (try wp_auto)
    wp_apply wp_preOk
    cases hp : preOkL x it.obj'
    · (try wp_auto)
      wp_apply wp_invalidObj
      iapply HΦ
      have : mupdateL x g = (g, invalidObjL x.Key') := by simp [mupdateL, hn, ← hit, hp]
      rw [this]
      iframe Hk
      ipureintro; exact ⟨Hr, rfl⟩
    (try wp_auto)
    wp_apply wp_updated x cur_ptr (DFrac.own 1) it.obj'.Name' it.obj'.UID' it.obj'.Value'
      it.obj'.ResourceVersion' $$ [$cur] as %q %err ⟨Hcur, Herr⟩
    cases hr : rejects x.Reject' it.obj'.Value'
    · isimp only [hr, Bool.false_eq_true, ↓reduceIte] at Herr
      icases Herr with ⟨%Herr, Hq⟩
      obtain ⟨rfl, Hqn⟩ := Herr
      (try wp_auto)
      wp_apply wp_sameObj
      have hmodel : ¬ (sameObjL (Obj.mk
          (if x.NoOp' = true then it.obj'.Name' else if it.obj'.Name' = [] then x.Key' else it.obj'.Name')
          it.obj'.UID' (if x.NoOp' = true then it.obj'.Value' else x.Val') it.obj'.ResourceVersion')
          it.obj' = true ∧ it.canon' = true) →
          mupdateL x g = (⟨setItemL g.items ⟨x.Key', Obj.mk
            (if x.NoOp' = true then it.obj'.Name' else if it.obj'.Name' = [] then x.Key' else it.obj'.Name')
            it.obj'.UID' (if x.NoOp' = true then it.obj'.Value' else x.Val') (g.rv + W64 1), true⟩,
            g.rv + W64 1⟩, objOutL (Obj.mk
            (if x.NoOp' = true then it.obj'.Name' else if it.obj'.Name' = [] then x.Key' else it.obj'.Name')
            it.obj'.UID' (if x.NoOp' = true then it.obj'.Value' else x.Val') (g.rv + W64 1))) := by
        intro hne
        simp only [mupdateL, updatedL_eq, hn, ← hit, ↓reduceIte, _root_.true_and, Bool.not_true,
          Bool.false_and, Bool.false_eq_true, hp, hr]
        rw [if_neg hne]
      cases hs : sameObjL (Obj.mk
          (if x.NoOp' = true then it.obj'.Name' else if it.obj'.Name' = [] then x.Key' else it.obj'.Name')
          it.obj'.UID' (if x.NoOp' = true then it.obj'.Value' else x.Val') it.obj'.ResourceVersion')
          it.obj'
      · (try wp_auto)
        have hm := hmodel (by simp [hs])
        set_tail
      · (try wp_auto)
        cases hc : it.canon'
        · (try simp only [hc])
          (try wp_auto)
          have hm := hmodel (by simp [hc])
          set_tail
        · (try simp only [hc])
          (try wp_auto)
          wp_apply wp_objOut
          iapply HΦ
          have : mupdateL x g = (g, objOutL it.obj') := by
            simp only [mupdateL, updatedL_eq, hn, ← hit, hr, hp]
            simp [hs, hc, hp, hr]
          rw [this]
          iframe Hk
          ipureintro; exact ⟨Hr, rfl⟩
    · isimp only [hr, ↓reduceIte, if_true] at Herr
      icases Hi with ⟨-, -, -, -, -, #EV⟩
      ihave %Hne := errVar_ne_nil _ err $$ [$EV $Herr]
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei =>
        (try wp_auto)
        iapply HΦ
        have : mupdateL x g = (g, rejectedL) := by simp [mupdateL, hn, ← hit, hr, hp]
        rw [this]
        iframe Hk
        ipureintro; exact ⟨Hr, rfl⟩

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
