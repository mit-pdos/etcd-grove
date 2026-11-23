module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__create
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.checkKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__ObjectResourceVersion
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__DeepCopyObject
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj__SetResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.NewKeyExistsError
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

theorem Model.create.wp_proof
    (wp_checkKey : checkKey.spec (GF := GF) (hG := hG))
    (wp_ObjRV : k8s_etcd3.versioner.ObjectResourceVersion.spec (GF := GF) (hG := hG))
    (wp_DeepCopy : k8s_etcd3.Obj.DeepCopyObject.spec (GF := GF) (hG := hG))
    (wp_SetRV : k8s_etcd3.Obj.SetResourceVersion.spec (GF := GF) (hG := hG))
    (wp_Exists : storage.NewKeyExistsError.spec (GF := GF) (hG := hG))
    (wp_Accessor : apimeta.Accessor.spec (GF := GF) (hG := hG))
    (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG)) :
    Model.create.spec (GF := GF) (hG := hG) := by
  intro mp m x op hsz
  wp_start as ⟨Hm, #Hop⟩
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
    have : rcreateL x m = failR m .other := by unfold rcreateL; simp [hk]
    rw [this]
    unfold failR respRep changeRep errRep deepRO deepRep
    simp only
    iframe Hinit
    isplitl [Hp HI HR]
    · iexists il, rl, M
      iframe
      iexact Hit
    isplitr
    · ipureintro; first | trivial | simp | exact ⟨rfl, nofun⟩ | exact nofun
    · ipureintro; first | trivial | simp | exact ⟨rfl, nofun⟩ | exact nofun
  have he : err = GoInterface.nil := Herr.2 hk
  subst he
  wp_auto
  wp_apply (wp_ObjRV op DFrac.discard (createObjL x)) $$ [Hop] as -
  · iexact Hop
  simp only
  wp_apply (wp_map_lookup2 go.string k8s_io.apimachinery.pkg.runtime.Object.ty il M
    (k8s_etcd3.storeKeyL x.Key') (DFrac.own 1)) $$ HI as HI
  ihave %hdom := itemsRO_dom M m.items (k8s_etcd3.storeKeyL x.Key') $$ Hit
  cases hs : M !! k8s_etcd3.storeKeyL x.Key' with
  | some v =>
    have hin : k8s_etcd3.storeKeyL x.Key' ∈ m.items :=
      (GMap.mem_iff _ _).2 (hdom.1 (by simp [hs]))
    simp only [Option.isSome_some, decide_true]
    wp_auto
    wp_apply +noauto (wp_Exists (m.pfx ++ k8s_etcd3.storeKeyL x.Key') (W64 0)) as %l Hl
    ipersist Hl
    wp_auto
    iapply HΦ
    have : rcreateL x m = failR m (existsE m (k8s_etcd3.storeKeyL x.Key')) := by
      unfold rcreateL; simp [hk, hin]
    rw [this]
    unfold failR respRep changeRep errRep deepRO deepRep existsE
    simp only
    iframe Hinit
    isplitl [Hp HI HR]
    · iexists il, rl, M
      iframe
      iexact Hit
    isplitl
    · isplitr
      · ipureintro; first | trivial | simp | exact ⟨rfl, nofun⟩ | exact nofun
      · rw [show (0 : w64) = W64 0 from rfl]
        iexists l, GoInterface.nil
        iframe Hl
        isplitr
        · ipureintro; rfl
        · iunfold deepRep
          ipureintro; rfl
    · ipureintro; first | trivial | simp | exact ⟨rfl, nofun⟩ | exact nofun
  | none =>
    have hnin : ¬ k8s_etcd3.storeKeyL x.Key' ∈ m.items := by
      intro h
      have h2 := (GMap.mem_iff _ _).1 h
      rw [← hdom, hs] at h2
      exact absurd h2 (by simp)
    simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
    wp_auto
    wp_apply (wp_DeepCopy op DFrac.discard (createObjL x)) $$ [Hop] as %c ⟨-, Hc⟩
    · iexact Hop
    have hty := (k8s_etcd3.objTyOk_holds).2.2
    wp_apply (wp_Accessor ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.ty, #c⟩ hty)
    wp_apply (wp_FormatUint (m.rv + W64 1) (W64 10)) as %str %hstr
    · ipureintro; decide
    wp_apply +noauto (wp_SetRV c (createObjL x) str) $$ [Hc] as Hc
    · iexact Hc
    have hrv : k8s_etcd3.setRVL str (W64 0) = m.rv + W64 1 := by
      rw [hstr]; exact k8s_etcd3.setRVL_decStr _ _
    rw [hrv]
    ipersist Hc
    wp_auto
    iapply wp_fupd
    wp_apply (wp_mapInsert go.string il M (k8s_etcd3.storeKeyL x.Key') (objIface c)) $$ HI as HI
    ipersist «$r1»
    imodintro
    iapply HΦ
    ihave #HD := itemsRO_insert M m.items (k8s_etcd3.storeKeyL x.Key') c ⟨(k8s_etcd3.splitKeyL x.Key').1, (k8s_etcd3.splitKeyL x.Key').2, x.UID', x.Val', x.Node', x.App', m.rv + W64 1, false⟩ (size_insert_le_of_lt _ _ _ hsz) $$ [Hit Hc]
    · isplitl
      · iexact Hit
      · iexact Hc
    obtain ⟨o, ho⟩ : ∃ o : Obj, o = ⟨(k8s_etcd3.splitKeyL x.Key').1, (k8s_etcd3.splitKeyL x.Key').2,
        x.UID', x.Val', x.Node', x.App', m.rv + W64 1, false⟩ := ⟨_, rfl⟩
    have hc : rcreateL x m =
        (⟨.obj o, .none⟩, RM.mk (<[k8s_etcd3.storeKeyL x.Key' := o]> m.items) (m.rv + W64 1) m.pfx m.rewrites,
          some ⟨k8s_etcd3.storeKeyL x.Key', m.rv + W64 1, some o, none⟩) := by
      subst ho; unfold rcreateL; simp [hk, hnin]
    rw [hc]
    subst ho
    unfold respRep changeRep errRep optObjD deepRO deepRep
    simp only
    iframe Hinit
    isplitl [Hp HI HR]
    · iexists il, rl, _
      iframe
      iexact HD
    isplitr
    · isplitl
      · iexists c
        iframe Hc
        ipureintro; rfl
      · ipureintro; first | trivial | simp | exact ⟨rfl, nofun⟩ | exact nofun
    · iexists _, _
      iframe «$r1»
      isplitl
      · iexists c
        iframe Hc
        ipureintro; rfl
      · ipureintro; rfl

end proof

end k8s_correctness
end EtcdGrove
end Perennial
