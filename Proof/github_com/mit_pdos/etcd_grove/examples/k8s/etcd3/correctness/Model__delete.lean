/-
Lean-first (no Rocq counterpart).

The proof of `(*Model).delete`: `checkKey`, the lookup ("not found"), `Preconditions.Check` on the
stored (read-only) object (`metaAt_obj`; the message is the model's, `preMsgL_kpre`), the
callback on a copy (`validateD`), and the delete at the next resource version (a copy of the stored
object with it, `SetResourceVersion(FormatUint(rv))`), both maps' entries removed.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__delete
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.checkKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__DeepCopyObject
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__SetResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.NewKeyNotFoundError
public import Spec.k8s_io.apiserver.pkg.storage.Preconditions__Check
public import Spec.k8s_io.apimachinery.pkg.api.meta.Accessor
public import Spec.strconv.FormatUint
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjSpec
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjRV
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ItemsRO

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Model.delete.wp_proof
    (wp_checkKey : checkKey.spec (GF := GF) (hG := hG))
    (wp_DeepCopy : k8s_etcd3.Obj.DeepCopyObject.spec (GF := GF) (hG := hG))
    (wp_SetRV : k8s_etcd3.Obj.SetResourceVersion.spec (GF := GF) (hG := hG))
    (wp_UID : k8s_etcd3.Obj.GetUID.spec (GF := GF) (hG := hG))
    (wp_RV : k8s_etcd3.Obj.GetResourceVersion.spec (GF := GF) (hG := hG))
    (wp_NotFound : storage.NewKeyNotFoundError.spec (GF := GF) (hG := hG))
    (wp_Check : storage.Preconditions.Check.spec (GF := GF) (hG := hG))
    (wp_Accessor : apimeta.Accessor.spec (GF := GF) (hG := hG))
    (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG)) :
    Model.delete.spec (GF := GF) (hG := hG) := by
  intro mp m x ctx pp vf hfit hvf
  wp_start as ⟨Hm, #Hpre, #Hvf⟩
  unfold modelOwn modelRep modelVal
  icases Hm with ⟨#Hinit, %il, %rl, %M, Hp, HI, #Hit, HR⟩
  wp_auto
  wp_apply (wp_checkKey (k8s_etcd3.storeKeyL x.Key') false) as %err %Herr
  by_cases hk : keyOkL (k8s_etcd3.storeKeyL x.Key') = true
  case neg =>
    have hne : err ≠ GoInterface.nil := fun h => hk (by unfold keyOkL; exact Herr.1 h)
    obtain ⟨ii, rfl⟩ : ∃ ii, err = GoInterface.ok ii := by
      cases err with
      | nil => exact absurd rfl hne
      | ok ii => exact ⟨ii, rfl⟩
    wp_auto
    iapply HΦ
    have : rdeleteL x m = failR m .other := by unfold rdeleteL; simp [hk]
    rw [this]
    unfold failR respRep changeRep errRep deepRO deepRep
    simp only
    iframe Hinit
    isplitl [Hp HI HR]
    · iexists il, rl, M
      iframe
      iexact Hit
    isplitr
    · ipureintro; trivial
    · ipureintro; trivial
  have he : err = GoInterface.nil := Herr.2 hk
  subst he
  wp_auto
  wp_apply (wp_map_lookup2 go.string k8s_io.apimachinery.pkg.runtime.Object.ty il M
    (k8s_etcd3.storeKeyL x.Key') (DFrac.own 1)) $$ HI as HI
  cases hs : M !! k8s_etcd3.storeKeyL x.Key' with
  | none =>
    ihave %hn := itemsRO_none M m.items (k8s_etcd3.storeKeyL x.Key') $$ Hit
    have hin : m.items !! k8s_etcd3.storeKeyL x.Key' = none := hn.1 hs
    simp only [Option.isSome_none]
    wp_auto
    wp_apply +noauto (wp_NotFound (m.pfx ++ k8s_etcd3.storeKeyL x.Key') _) as %l Hl
    ipersist Hl
    wp_auto
    iapply HΦ
    have : rdeleteL x m = failR m (notFoundE m (k8s_etcd3.storeKeyL x.Key')) := by
      unfold rdeleteL; simp [hk, hin]
    rw [this]
    unfold failR respRep changeRep errRep deepRO deepRep notFoundE
    simp only
    iframe Hinit
    isplitl [Hp HI HR]
    · iexists il, rl, M
      iframe
      iexact Hit
    isplitl
    · isplitr
      · ipureintro; trivial
      · iexists l, GoInterface.nil
        iframe Hl
        isplitr
        · ipureintro; rfl
        · iunfold deepRep
          ipureintro; rfl
    · ipureintro; trivial
  | some v =>
    icases itemsRO_lookup M m.items _ v hs $$ Hit with ⟨%p, %o, ⟨%ho, %hv⟩, #Hpo⟩
    subst hv
    simp only [Option.isSome_some]
    wp_auto
    have hty := (k8s_etcd3.objTyOk_holds)
    ihave #Hmeta := metaAt_obj wp_UID wp_RV hty p DFrac.discard o $$ Hinit
    wp_apply (wp_Check pp (k8s_etcd3.kpreOf x) (m.pfx ++ k8s_etcd3.storeKeyL x.Key') (objIface p)
      (p ↦□ o) o.UID' (k8s_etcd3.rvStr o.ResourceVersion')) $$ [] as %e1 ⟨-, Hck⟩
    · isplitr
      · iexact Hpre
      isplitr
      · iexact Hmeta
      · iexact Hpo
    rw [kpreOf_ok x o]
    cases hpok : k8s_etcd3.preOkL x o
    · isimp only [Bool.false_eq_true, ↓reduceIte] at Hck
      ihave #Hck' := Hck
      iunfold k8s.invalidErrMsg at Hck'
      icases Hck' with ⟨%l, %q, %hl, #Hl, #Hq⟩
      subst hl
      wp_auto
      iapply HΦ
      have : rdeleteL x m = failR m (invalidE m (k8s_etcd3.storeKeyL x.Key')
          ((k8s_etcd3.kpreOf x).failMsg o.UID' (k8s_etcd3.rvStr o.ResourceVersion'))) := by
        unfold rdeleteL; simp [hk, ho, preMsgL_kpre x o hpok]
      rw [this]
      unfold failR respRep changeRep errRep deepRO deepRep invalidE
      simp only
      iframe Hinit
      isplitl [Hp HI HR]
      · iexists il, rl, M
        iframe
        iexact Hit
      isplitl
      · isplitr
        · ipureintro; trivial
        · rw [show (0 : w64) = W64 0 from rfl]
          iexists l
          iexists _
          isplitr
          · ipureintro; rfl
          isplitr
          · iexact Hl
          · iunfold deepRep
            iexists q
            iframe Hq
            ipureintro; rfl
      · ipureintro; trivial
    · isimp only [↓reduceIte] at Hck
      icases Hck with %he1
      subst he1
      wp_auto
      rw [decide_eq_false hvf]
      wp_auto
      wp_apply (wp_DeepCopy p DFrac.discard o) $$ [Hpo] as %c ⟨-, Hc⟩
      · iexact Hpo
      wp_bind
      ihave #Hvf' := Hvf
      iunfold k8s_etcd3.validateD at Hvf'
      iapply Hvf' $$ %ctx %c %o %_ Hc
      inext
      iintro %err Hc Herr
      wp_auto
      cases hrj : k8s_etcd3.rejects x.HasReject' x.Reject' o.Node'
      · isimp only [Bool.false_eq_true, ↓reduceIte] at Herr
        icases Herr with %herr
        subst herr
        wp_auto
        wp_apply (wp_DeepCopy p DFrac.discard o) $$ [Hpo] as %d ⟨-, Hd⟩
        · iexact Hpo
        wp_apply (wp_Accessor ⟨go.GoType.PointerType
          github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty, #d⟩ hty.2.2)
        wp_apply (wp_FormatUint (m.rv + W64 1) (W64 10)) as %str %hstr
        · ipureintro; decide
        wp_apply +noauto (wp_SetRV d o str) $$ [Hd] as Hd
        · iexact Hd
        have hrv : k8s_etcd3.setRVL str o.ResourceVersion' = m.rv + W64 1 := by
          rw [hstr]; exact k8s_etcd3.setRVL_decStr _ _
        rw [hrv]
        ipersist Hd
        wp_auto
        iapply wp_fupd
        wp_apply (wp_mapDelete il M (k8s_etcd3.storeKeyL x.Key') go.string
          k8s_io.apimachinery.pkg.runtime.Object.ty) $$ HI as HI
        wp_apply (wp_mapDelete rl m.rewrites (k8s_etcd3.storeKeyL x.Key') go.string go.bool) $$ HR
          as HR
        ipersist «$r1»
        imodintro
        iapply HΦ
        have hd : rdeleteL x m = (⟨.obj { o with ResourceVersion' := m.rv + W64 1 }, .none⟩,
            RM.mk (GMap.delete (k8s_etcd3.storeKeyL x.Key') m.items) (m.rv + W64 1) m.pfx
              (GMap.delete (k8s_etcd3.storeKeyL x.Key') m.rewrites),
            some ⟨k8s_etcd3.storeKeyL x.Key', m.rv + W64 1, none, some o⟩) := by
          unfold rdeleteL; simp [hk, ho, (preMsgL_none x o).2 hpok, hrj]
        rw [hd]
        unfold respRep changeRep errRep optObjD deepRO deepRep
        simp only
        iframe Hinit
        isplitl [Hp HI HR]
        · iexists il, rl, _
          iframe
          iapply itemsRO_delete $$ Hit
        isplitr
        · isplitl
          · iexists d
            isplitr
            · ipureintro; rfl
            · iexact Hd
          · ipureintro; trivial
        · iexists _, _
          iframe «$r1»
          isplitr
          · ipureintro; rfl
          · iexists p
            iframe Hpo
            ipureintro; rfl
      · isimp only [↓reduceIte] at Herr
        ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
        · iapply isPkgInit_access $$ Hinit
        icases Hi with ⟨-, -, -, #HeD, -⟩
        ihave #Hd := errVar_deep _ _ err $$ [$HeD $Herr]
        ihave #Hd' := Hd
        iunfold deepRep at Hd'
        icases Hd' with ⟨%le, %hle, -⟩
        subst hle
        wp_auto
        iapply HΦ
        have : rdeleteL x m = failR m delRejE := by
          unfold rdeleteL; simp [hk, ho, (preMsgL_none x o).2 hpok, hrj]
        rw [this]
        unfold failR respRep changeRep errRep delRejE
        simp only
        iframe Hinit Hd
        isplitl [Hp HI HR]
        · iexists il, rl, M
          iframe
          iexact Hit
        iunfold deepRep
        iclear «$res0» «$res1»
        ipureintro; trivial

end proof

end k8s_correctness
end EtcdGrove
end Perennial
