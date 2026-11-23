/-
Lean-first (no Rocq counterpart).

The proof of `(*Model).update`: `checkKey`, the lookup ("not found", or `NewFunc()`'s zero object
under `ignoreNotFound`), `Preconditions.Check` on the current object (a copy of the stored one:
`metaAt_obj`; the message is the model's, `checkMsgL_kpre`), the callback (`tryUpdateD`, on the
current object as an `objAtD`: `itemsFitL`), the no-op shortcut (D30g: unless the key needs a
rewrite; `reflect.DeepEqual` of the two objects with their resource versions cleared) and the write
at the next resource version.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__update
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.checkKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__DeepCopyObject
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__SetResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.NewKeyNotFoundError
public import Spec.k8s_io.apiserver.pkg.storage.Preconditions__Check
public import Spec.k8s_io.apimachinery.pkg.api.meta.Accessor
public import Spec.strconv.FormatUint
public import Spec.reflect.DeepEqualK8s
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newObj
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__ObjectResourceVersion
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

theorem newObj_ne_nil :
    functions github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newObj [] ≠ func.nil := by
  intro h
  have hu := FuncUnfold.func_unfold (f := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newObj)
    (type_args := [])
  rw [h, go.intoVal_unfold GoFunc] at hu
  simp [func.nil, github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newObj.impl] at hu

theorem Model.update.wp_proof
    (wp_checkKey : checkKey.spec (GF := GF) (hG := hG))
    (wp_newObj : k8s_etcd3.newObj.spec (GF := GF) (hG := hG))
    (wp_ObjRV : k8s_etcd3.versioner.ObjectResourceVersion.spec (GF := GF) (hG := hG))
    (wp_DeepCopy : k8s_etcd3.Obj.DeepCopyObject.spec (GF := GF) (hG := hG))
    (wp_SetRV : k8s_etcd3.Obj.SetResourceVersion.spec (GF := GF) (hG := hG))
    (wp_UID : k8s_etcd3.Obj.GetUID.spec (GF := GF) (hG := hG))
    (wp_RV : k8s_etcd3.Obj.GetResourceVersion.spec (GF := GF) (hG := hG))
    (wp_NotFound : storage.NewKeyNotFoundError.spec (GF := GF) (hG := hG))
    (wp_Check : storage.Preconditions.Check.spec (GF := GF) (hG := hG))
    (wp_Accessor : apimeta.Accessor.spec (GF := GF) (hG := hG))
    (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG))
    (wp_DE : reflect.DeepEqual.spec_k8s (GF := GF) (hG := hG)) :
    Model.update.spec (GF := GF) (hG := hG) := by
  intro mp m x ctx pp uf cx hfit hfx huf hsz
  wp_start as ⟨Hm, #Hpre, #Huf⟩
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
    have : rupdateL x m = failR m .other := by unfold rupdateL; simp [hk]
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
  rw [decide_eq_false huf]
  wp_auto
  have hty := (k8s_etcd3.objTyOk_holds)
  wp_apply (wp_map_lookup2 go.string k8s_io.apimachinery.pkg.runtime.Object.ty il M
    (k8s_etcd3.storeKeyL x.Key') (DFrac.own 1)) $$ HI as HI
  cases hs : M !! k8s_etcd3.storeKeyL x.Key' with
  | none =>
    ihave %hn := itemsRO_none M m.items (k8s_etcd3.storeKeyL x.Key') $$ Hit
    have hin : m.items !! k8s_etcd3.storeKeyL x.Key' = none := hn.1 hs
    simp only [Option.isSome_none]
    wp_auto
    cases hig : x.IgnoreNotFound'
    · wp_auto
      wp_apply +noauto (wp_NotFound (m.pfx ++ k8s_etcd3.storeKeyL x.Key') _) as %l Hl
      ipersist Hl
      wp_auto
      iapply HΦ
      have : rupdateL x m = failR m (notFoundE m (k8s_etcd3.storeKeyL x.Key')) := by
        unfold rupdateL; simp [hk, hin, hig]
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
    · wp_auto
      rw [decide_eq_false newObj_ne_nil]
      wp_auto
      wp_apply +noauto wp_newObj as %co Ho
      wp_auto
      ihave #Hmeta := metaAt_objAtD wp_UID wp_RV hty co k8s_etcd3.dzero [] $$ Hinit
      wp_apply (wp_Check pp (k8s_etcd3.kpreOf x) (m.pfx ++ k8s_etcd3.storeKeyL x.Key') co
        _ k8s_etcd3.dzero.uid []) $$ [Ho] as %e1 ⟨Ho, Hck⟩
      · isplitr
        · iexact Hpre
        isplitr
        · iexact Hmeta
        · iexact Ho
      have hok : (k8s_etcd3.kpreOf x).ok [] [] = k8s_etcd3.preOkL x k8s_etcd3.zObj :=
        kpreOf_ok x k8s_etcd3.zObj
      cases hpok : k8s_etcd3.preOkL x k8s_etcd3.zObj
      · isimp only [hok, hpok, Bool.false_eq_true, ↓reduceIte] at Hck
        ihave #Hck' := Hck
        iunfold k8s.invalidErrMsg at Hck'
        icases Hck' with ⟨%l, %q, %hl, #Hl, #Hq⟩
        subst hl
        wp_auto
        iapply HΦ
        have hmsg : checkMsgL x k8s_etcd3.zObj = some ((k8s_etcd3.kpreOf x).failMsg [] []) :=
          checkMsgL_kpre x k8s_etcd3.zObj hpok
        have : rupdateL x m = failR m (invalidE m (k8s_etcd3.storeKeyL x.Key')
            ((k8s_etcd3.kpreOf x).failMsg [] [])) := by
          unfold rupdateL; simp [hk, hin, hig, hmsg]
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
              isplitr
              · ipureintro; rfl
              · iexact Hq
        · ipureintro; trivial
      · isimp only [hok, hpok, ↓reduceIte] at Hck
        icases Hck with %he1
        subst he1
        wp_auto
        wp_bind
        ihave #Huf' := Huf
        iunfold k8s_etcd3.tryUpdateD at Huf'
        have hz : k8s_etcd3.rvStr (W64 0) = [] := rfl
        rw [show (0 : w64) = W64 0 from rfl]
        iapply Huf' $$ %co %k8s_etcd3.dzero %(W64 0) %_ [Ho]
        · rw [hz]; iexact Ho
        inext
        iintro %ret %ttlp %err Hres
        wp_auto
        cases hrj : k8s_etcd3.rejects x.HasReject' x.Reject' k8s_etcd3.zObj.Node'
        · have hrj' : k8s_etcd3.rejects x.HasReject' x.Reject' k8s_etcd3.dzero.node = false := hrj
          isimp only [hrj', Bool.false_eq_true, ↓reduceIte] at Hres
          icases Hres with ⟨⟨%herr, %httl⟩, Hu⟩
          subst herr httl
          wp_auto
          iunfold k8s_etcd3.objAtD at Hu
          icases Hu with ⟨%pu, %nu, ⟨%hret, -, %hnu⟩, Hpu⟩
          subst hret
          have hn0 : nu = W64 0 := (k8s_etcd3.rvStr_inj hnu).symm
          subst hn0
          wp_auto
          wp_apply (wp_DeepCopy pu (DFrac.own 1) _) $$ [Hpu] as %c2 ⟨-, Hc2⟩
          · iexact Hpu
          wp_apply (wp_Accessor ⟨go.GoType.PointerType
            github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty, #c2⟩ hty.2.2)
          wp_apply (wp_FormatUint (m.rv + W64 1) (W64 10)) as %str %hstr
          · ipureintro; decide
          wp_apply +noauto (wp_SetRV c2 _ str) $$ [Hc2] as Hc2
          · iexact Hc2
          have hrv : ∀ old, k8s_etcd3.setRVL str old = m.rv + W64 1 := by
            intro old; rw [hstr]; exact k8s_etcd3.setRVL_decStr _ _
          rw [hrv]
          ipersist Hc2
          wp_auto
          iapply wp_fupd
          wp_apply (wp_mapInsert go.string il M (k8s_etcd3.storeKeyL x.Key') (objIface c2)) $$ HI
            as HI
          wp_apply (wp_mapDelete rl m.rewrites (k8s_etcd3.storeKeyL x.Key') go.string go.bool) $$ HR
            as HR
          ipersist «$r1»
          imodintro
          iapply HΦ
          have hu : (k8s_etcd3.updObj x k8s_etcd3.dzero).toObj (W64 0) =
              k8s_etcd3.updGo x k8s_etcd3.zObj := k8s_etcd3.updObj_toObj x k8s_etcd3.dzero 0 hfx
          have hd : rupdateL x m = updWriteL m (k8s_etcd3.storeKeyL x.Key') none
              (k8s_etcd3.updGo x k8s_etcd3.zObj) := by
            unfold rupdateL; simp [hk, hin, hig, (checkMsgL_none x k8s_etcd3.zObj).2 hpok, hrj]
          rw [hd]
          ihave #HD := itemsRO_insert M m.items (k8s_etcd3.storeKeyL x.Key') c2
            { k8s_etcd3.updGo x k8s_etcd3.zObj with ResourceVersion' := m.rv + W64 1 }
            (size_insert_le_of_lt _ _ _ hsz) $$ [Hit Hc2]
          · isplitl
            · iexact Hit
            · rw [← hu]; iexact Hc2
          unfold updWriteL respRep changeRep errRep optObjD deepRO deepRep
          simp only
          iframe Hinit
          isplitl [Hp HI HR]
          · iexists il, rl, _
            iframe
            iexact HD
          isplitr
          · isplitl
            · iexists c2
              isplitr
              · ipureintro; rfl
              · rw [← hu]; iexact Hc2
            · ipureintro; trivial
          · iexists _, _
            iframe «$r1»
            isplitl
            · iexists c2
              isplitr
              · ipureintro; rfl
              · rw [← hu]; iexact Hc2
            · ipureintro; rfl
        · have hrj' : k8s_etcd3.rejects x.HasReject' x.Reject' k8s_etcd3.dzero.node = true := hrj
          isimp only [hrj', ↓reduceIte] at Hres
          ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
          · iapply isPkgInit_access $$ Hinit
          icases Hi with ⟨-, -, -, -, #HeU⟩
          ihave #Hd := errVar_deep _ _ err $$ [$HeU $Hres]
          ihave #Hd' := Hd
          iunfold deepRep at Hd'
          icases Hd' with ⟨%le, %hle, -⟩
          subst hle
          wp_auto
          iapply HΦ
          have : rupdateL x m = failR m updRejE := by
            unfold rupdateL; simp [hk, hin, hig, (checkMsgL_none x k8s_etcd3.zObj).2 hpok, hrj]
          rw [this]
          unfold failR respRep changeRep errRep updRejE
          simp only
          iframe Hinit Hd
          isplitl [Hp HI HR]
          · iexists il, rl, M
            iframe
            iexact Hit
          iunfold deepRep
          iclear «$res0» «$res1»
          ipureintro; trivial
  | some v =>
    icases itemsRO_lookup M m.items _ v hs $$ Hit with ⟨%p, %o, ⟨%ho, %hv⟩, #Hpo⟩
    subst hv
    simp only [Option.isSome_some]
    obtain ⟨hf, ha⟩ := hfit _ _ ho
    have hoo : (k8s_etcd3.DObj.ofObj o hf).toObj o.ResourceVersion' = o := by
      rw [k8s_etcd3.DObj.ofObj_toObj_rv o hf ha]
    wp_auto
    wp_apply (wp_DeepCopy p DFrac.discard o) $$ [Hpo] as %c ⟨-, Hc⟩
    · iexact Hpo
    wp_apply (wp_ObjRV p DFrac.discard o) $$ [Hpo] as -
    · iexact Hpo
    ihave Ho := objAtD_of_fit c o hf ha $$ Hc
    ihave #Hmeta := metaAt_objAtD wp_UID wp_RV hty (objIface c) (k8s_etcd3.DObj.ofObj o hf)
      (k8s_etcd3.rvStr o.ResourceVersion') $$ Hinit
    have huid : (k8s_etcd3.DObj.ofObj o hf).uid = o.UID' := rfl
    isimp only [huid] at Hmeta
    wp_apply (wp_Check pp (k8s_etcd3.kpreOf x) (m.pfx ++ k8s_etcd3.storeKeyL x.Key') (objIface c)
      _ o.UID' (k8s_etcd3.rvStr o.ResourceVersion')) $$ [Ho] as %e1 ⟨Ho, Hck⟩
    · isplitr
      · iexact Hpre
      isplitr
      · iexact Hmeta
      · iexact Ho
    rw [kpreOf_ok x o]
    cases hpok : k8s_etcd3.preOkL x o
    · isimp only [Bool.false_eq_true, ↓reduceIte] at Hck
      ihave #Hck' := Hck
      iunfold k8s.invalidErrMsg at Hck'
      icases Hck' with ⟨%l, %q, %hl, #Hl, #Hq⟩
      subst hl
      wp_auto
      iapply HΦ
      have : rupdateL x m = failR m (invalidE m (k8s_etcd3.storeKeyL x.Key')
          ((k8s_etcd3.kpreOf x).failMsg o.UID' (k8s_etcd3.rvStr o.ResourceVersion'))) := by
        unfold rupdateL; simp [hk, ho, checkMsgL_kpre x o hpok]
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
            isplitr
            · ipureintro; rfl
            · iexact Hq
      · ipureintro; trivial
    · isimp only [↓reduceIte] at Hck
      icases Hck with %he1
      subst he1
      wp_auto
      wp_bind
      ihave #Huf' := Huf
      iunfold k8s_etcd3.tryUpdateD at Huf'
      rw [show (0 : w64) = W64 0 from rfl]
      iapply Huf' $$ %(objIface c) %(k8s_etcd3.DObj.ofObj o hf) %o.ResourceVersion' %_ [Ho]
      · iexact Ho
      inext
      iintro %ret %ttlp %err Hres
      wp_auto
      cases hrj : k8s_etcd3.rejects x.HasReject' x.Reject' o.Node'
      · have hrj' : k8s_etcd3.rejects x.HasReject' x.Reject'
            (k8s_etcd3.DObj.ofObj o hf).node = false := hrj
        isimp only [hrj', Bool.false_eq_true, ↓reduceIte] at Hres
        icases Hres with ⟨⟨%herr, %httl⟩, Hu⟩
        subst herr httl
        wp_auto
        iunfold k8s_etcd3.objAtD at Hu
        icases Hu with ⟨%pu, %nu, ⟨%hret, -, %hnu⟩, Hpu⟩
        subst hret
        have hn0 : nu = o.ResourceVersion' := (k8s_etcd3.rvStr_inj hnu).symm
        subst hn0
        have hu : (k8s_etcd3.updObj x (k8s_etcd3.DObj.ofObj o hf)).toObj o.ResourceVersion' =
            k8s_etcd3.updGo x o := by
          rw [k8s_etcd3.updObj_toObj x _ _ hfx, hoo]
        rw [hu]
        wp_apply (wp_map_lookup1 go.string go.bool rl m.rewrites (k8s_etcd3.storeKeyL x.Key')
          (DFrac.own 1)) $$ HR as HR
        have hnrd : (m.rewrites !! k8s_etcd3.storeKeyL x.Key').getD (zero_val Bool) =
            needsRewriteL m (k8s_etcd3.storeKeyL x.Key') := rfl
        rw [hnrd]
        cases hnr : needsRewriteL m (k8s_etcd3.storeKeyL x.Key')
        · wp_auto
          wp_apply (wp_DeepCopy p DFrac.discard o) $$ [Hpo] as %d1 ⟨-, Hd1⟩
          · iexact Hpo
          wp_apply (wp_Accessor ⟨go.GoType.PointerType
            github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty, #d1⟩ hty.2.2)
          wp_apply +noauto (wp_SetRV d1 o _) $$ [Hd1] as Hd1
          · iexact Hd1
          wp_auto
          wp_apply (wp_DeepCopy pu (DFrac.own 1) (k8s_etcd3.updGo x o)) $$ [Hpu] as %d2 ⟨Hpu, Hd2⟩
          · iexact Hpu
          wp_apply (wp_Accessor ⟨go.GoType.PointerType
            github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty, #d2⟩ hty.2.2)
          wp_apply +noauto (wp_SetRV d2 (k8s_etcd3.updGo x o) _) $$ [Hd2] as Hd2
          · iexact Hd2
          wp_auto
          have h0 : ∀ v, k8s_etcd3.setRVL [] v = 0 := fun _ => rfl
          isimp only [h0] at Hd1 Hd2
          wp_apply (wp_DE.1 (objIface d1) (objIface d2) (.obj { o with ResourceVersion' := 0 })
            (.obj { k8s_etcd3.updGo x o with ResourceVersion' := 0 }) (DFrac.own 1) (DFrac.own 1))
            $$ [Hd1 Hd2] as %b ⟨%hb, -, -⟩
          · unfold deepRep
            isplitl [Hd1]
            · iexists d1
              isplitr
              · ipureintro; rfl
              · iexact Hd1
            · iexists d2
              isplitr
              · ipureintro; rfl
              · iexact Hd2
          cases b
          · wp_auto
            wp_apply (wp_DeepCopy pu (DFrac.own 1) (k8s_etcd3.updGo x o)) $$ [Hpu] as %c2 ⟨-, Hc2⟩
            · iexact Hpu
            wp_apply (wp_Accessor ⟨go.GoType.PointerType
              github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty, #c2⟩ hty.2.2)
            wp_apply (wp_FormatUint (m.rv + W64 1) (W64 10)) as %str %hstr
            · ipureintro; decide
            wp_apply +noauto (wp_SetRV c2 _ str) $$ [Hc2] as Hc2
            · iexact Hc2
            have hrv : ∀ old, k8s_etcd3.setRVL str old = m.rv + W64 1 := by
              intro old; rw [hstr]; exact k8s_etcd3.setRVL_decStr _ _
            rw [hrv]
            ipersist Hc2
            wp_auto
            iapply wp_fupd
            wp_apply (wp_mapInsert go.string il M (k8s_etcd3.storeKeyL x.Key') (objIface c2)) $$ HI
              as HI
            wp_apply (wp_mapDelete rl m.rewrites (k8s_etcd3.storeKeyL x.Key') go.string go.bool)
              $$ HR as HR
            ipersist «$r1»
            imodintro
            iapply HΦ
            have hd : rupdateL x m = updWriteL m (k8s_etcd3.storeKeyL x.Key') (some o)
                (k8s_etcd3.updGo x o) := by
              have hne' : ¬ ({ o with ResourceVersion' := 0 } =
                  { k8s_etcd3.updGo x o with ResourceVersion' := 0 }) := fun h => by
                rw [h] at hb; simp at hb
              unfold rupdateL
              simp [hk, ho, (checkMsgL_none x o).2 hpok, hrj, hnr,
                -github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.mk.injEq]
              intro h; exfalso; apply hne'; simpa using h
            rw [hd]
            ihave #HD := itemsRO_insert M m.items (k8s_etcd3.storeKeyL x.Key') c2
              { k8s_etcd3.updGo x o with ResourceVersion' := m.rv + W64 1 }
              (size_insert_le_of_lt _ _ _ hsz) $$ [Hit Hc2]
            · isplitl
              · iexact Hit
              · iexact Hc2
            unfold updWriteL respRep changeRep errRep optObjD deepRO deepRep
            simp only
            iframe Hinit
            isplitl [Hp HI HR]
            · iexists il, rl, _
              iframe
              iexact HD
            isplitr
            · isplitl
              · iexists c2
                isplitr
                · ipureintro; rfl
                · iexact Hc2
              · ipureintro; trivial
            · iexists _, _
              iframe «$r1»
              isplitl
              · iexists c2
                isplitr
                · ipureintro; rfl
                · iexact Hc2
              · iexists p
                iframe Hpo
                ipureintro; rfl
          · wp_auto
            iapply wp_fupd
            wp_apply (wp_DeepCopy p DFrac.discard o) $$ [Hpo] as %d3 ⟨-, Hd3⟩
            · iexact Hpo
            ipersist Hd3
            (try wp_auto)
            imodintro
            iapply HΦ
            have heq : { o with ResourceVersion' := 0 } =
                { k8s_etcd3.updGo x o with ResourceVersion' := 0 } := by
              have := hb.1 rfl; injection this
            have hd : rupdateL x m = (⟨.obj o, .none⟩, m, none) := by
              unfold rupdateL
              simp [hk, ho, (checkMsgL_none x o).2 hpok, hrj, hnr,
                -github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.mk.injEq]
              intro h; exfalso; apply h; simpa using heq
            rw [hd]
            unfold respRep changeRep errRep deepRO deepRep
            simp only
            iframe Hinit
            isplitl [Hp HI HR]
            · iexists il, rl, M
              iframe
              iexact Hit
            isplitr
            · isplitl
              · iexists d3
                isplitr
                · ipureintro; rfl
                · iexact Hd3
              · ipureintro; trivial
            · iclear «$res0» «$res1»
              ipureintro; trivial
        · wp_auto
          wp_apply (wp_DeepCopy pu (DFrac.own 1) (k8s_etcd3.updGo x o)) $$ [Hpu] as %c2 ⟨-, Hc2⟩
          · iexact Hpu
          wp_apply (wp_Accessor ⟨go.GoType.PointerType
            github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty, #c2⟩ hty.2.2)
          wp_apply (wp_FormatUint (m.rv + W64 1) (W64 10)) as %str %hstr
          · ipureintro; decide
          wp_apply +noauto (wp_SetRV c2 _ str) $$ [Hc2] as Hc2
          · iexact Hc2
          have hrv : ∀ old, k8s_etcd3.setRVL str old = m.rv + W64 1 := by
            intro old; rw [hstr]; exact k8s_etcd3.setRVL_decStr _ _
          rw [hrv]
          ipersist Hc2
          wp_auto
          iapply wp_fupd
          wp_apply (wp_mapInsert go.string il M (k8s_etcd3.storeKeyL x.Key') (objIface c2)) $$ HI
            as HI
          wp_apply (wp_mapDelete rl m.rewrites (k8s_etcd3.storeKeyL x.Key') go.string go.bool) $$ HR
            as HR
          ipersist «$r1»
          imodintro
          iapply HΦ
          have hd : rupdateL x m = updWriteL m (k8s_etcd3.storeKeyL x.Key') (some o)
              (k8s_etcd3.updGo x o) := by
            unfold rupdateL; simp [hk, ho, (checkMsgL_none x o).2 hpok, hrj, hnr]
          rw [hd]
          ihave #HD := itemsRO_insert M m.items (k8s_etcd3.storeKeyL x.Key') c2
            { k8s_etcd3.updGo x o with ResourceVersion' := m.rv + W64 1 }
            (size_insert_le_of_lt _ _ _ hsz) $$ [Hit Hc2]
          · isplitl
            · iexact Hit
            · iexact Hc2
          unfold updWriteL respRep changeRep errRep optObjD deepRO deepRep
          simp only
          iframe Hinit
          isplitl [Hp HI HR]
          · iexists il, rl, _
            iframe
            iexact HD
          isplitr
          · isplitl
            · iexists c2
              isplitr
              · ipureintro; rfl
              · iexact Hc2
            · ipureintro; trivial
          · iexists _, _
            iframe «$r1»
            isplitl
            · iexists c2
              isplitr
              · ipureintro; rfl
              · iexact Hc2
            · iexists p
              iframe Hpo
              ipureintro; rfl
      · have hrj' : k8s_etcd3.rejects x.HasReject' x.Reject'
            (k8s_etcd3.DObj.ofObj o hf).node = true := hrj
        isimp only [hrj', ↓reduceIte] at Hres
        ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
        · iapply isPkgInit_access $$ Hinit
        icases Hi with ⟨-, -, -, -, #HeU⟩
        ihave #Hd := errVar_deep _ _ err $$ [$HeU $Hres]
        ihave #Hd' := Hd
        iunfold deepRep at Hd'
        icases Hd' with ⟨%le, %hle, -⟩
        subst hle
        wp_auto
        iapply HΦ
        have : rupdateL x m = failR m updRejE := by
          unfold rupdateL; simp [hk, ho, (checkMsgL_none x o).2 hpok, hrj]
        rw [this]
        unfold failR respRep changeRep errRep updRejE
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
