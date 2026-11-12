/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/store__finalizeList.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__finalizeList
public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__SetShardInfoOnList
public import Spec.reflect.Value__IsNil
public import Spec.reflect.Value__Type
public import Spec.reflect.Value__Set

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver reflectM

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.finalizeList.wp_proof
    (wp_IsNil : reflect.Value.IsNil.spec (GF := GF) (hG := hG))
    (wp_Type : reflect.Value.Type.spec (GF := GF) (hG := hG))
    (wp_Set : reflect.Value.Set.spec (GF := GF) (hG := hG))
    (wp_SetShard : storage.SelectionPredicate.SetShardInfoOnList.spec (GF := GF) (hG := hG)) :
    store.finalizeList.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c L lx pl pred sel emp rev cont rem remV ag v os rv0 cont0 rem0 hlx
  subst hlx
  wp_start as ⟨#Hst, #Hlc, #Hsel, Hag, %hv, Hl, Hrem⟩
  ihave #Pr : isPkgInit (PROP := IProp GF) pkg_id.reflect $$ []
  · iPkgInit
  ihave #Ps : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  iunfold isStore at Hst
  icases Hst with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, -⟩
  iunfold listContractOk at Hlc
  icases Hlc with ⟨#Hlc', -, #HUpd, -⟩
  iunfold listContractOk' at Hlc'
  icases Hlc' with ⟨-, #HM0, -, -⟩
  iunfold selPredOk at Hsel
  icases Hsel with ⟨%hsel, -⟩
  iunfold freshAggr at Hag
  icases Hag with ⟨%ii, %hag, Hagg⟩
  subst hag
  iunfold ListSpec.listAtItems at Hl
  icases Hl with ⟨%hpl, %s, Hp, Hit, Hmeta⟩
  wp_auto
  wp_bind
  iapply Hagg
  inext
  wp_auto
  wp_apply (wp_IsNil v_ptr _ _ v c.S.objTy (L.itemsRef pl) s) $$ [$v $Hp] as %b ⟨%hb, v, Hp⟩
  · ipureintro; exact hv
  cases b
  · wp_auto
    wp_bind
    iapply HUpd $$ %pl %os %rv0 %rev %cont0 %cont %rem %remV %rem0 [Hp Hit Hmeta] Hrem
    · iunfold ListSpec.listAtItems
      isplitr
      · ipureintro; exact hpl
      iexists s
      iframe
    inext
    iintro %err ⟨%he, Hl⟩
    subst he
    wp_auto
    wp_apply (wp_SetShard pred_ptr _ pred _ hsel.1) $$ [$pred] as -
    iapply HΦ
    iunfold ListSpec.listAt
    iexists pl
    iframe
    ipureintro; rfl
  · icases persistent_entails_left (L.itemsAt_len s os) $$ Hit with ⟨Hit, %Hlen⟩
    have hos : os = [] := List.eq_nil_of_length_eq_zero (by rw [← Hlen]; have := hb rfl; word)
    subst hos
    wp_auto
    wp_apply (wp_Type v_ptr _ v _ _) $$ [$v] as %rt ⟨v, %hrt⟩
    · ipureintro; exact hv
    wp_bind
    iapply HM0 $$ %rt %(W64 0)
    · ipureintro; refine ⟨hrt, ?_, ?_⟩ <;> word
    inext
    iintro %w %s' %hw Hit'
    (try wp_auto)
    wp_apply (wp_Set v_ptr _ v w (go.GoType.SliceType c.S.objTy) (L.itemsRef pl) GoSlice s s')
      $$ [$v $Hp] as ⟨v, Hp⟩
    · ipureintro; exact ⟨hv, Or.inr ⟨c.S.objTy, s', rfl, hw, HEq.rfl⟩⟩
    (try wp_auto)
    wp_bind
    iapply HUpd $$ %pl %([] : List (Obj × GoString)) %rv0 %rev %cont0 %cont %rem %remV %rem0 [Hp Hit' Hmeta] Hrem
    · iunfold ListSpec.listAtItems
      isplitr
      · ipureintro; exact hpl
      iexists s'
      iframe
    inext
    iintro %err ⟨%he, Hl⟩
    subst he
    wp_auto
    wp_apply (wp_SetShard pred_ptr _ pred _ hsel.1) $$ [$pred] as -
    iapply HΦ
    iunfold ListSpec.listAt
    iexists pl
    iframe
    ipureintro; rfl

end proof

end k8s
end EtcdGrove
end Perennial
