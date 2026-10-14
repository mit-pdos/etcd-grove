/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/DoubleBarrier__Enter.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.DoubleBarrier__Enter
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.DoubleBarrier__enteredClients
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newUniqueEphemeralKey
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.RemoteKV__Delete
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.RemoteKV__Revision
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.WaitEvents
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Client

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem DoubleBarrier.Enter.wp_proof
    (wp_Client : concurrency.Session.Client.spec (GF := GF) (hG := hG))
    (wp_enteredClients : DoubleBarrier.enteredClients.spec (GF := GF) (hG := hG))
    (wp_newUniqueEphemeralKey : newUniqueEphemeralKey.spec (GF := GF) (hG := hG))
    (wp_Delete : RemoteKV.Delete.spec (GF := GF) (hG := hG))
    (wp_Revision : RemoteKV.Revision.spec (GF := GF) (hG := hG))
    (wp_WaitEvents : WaitEvents.spec (GF := GF) (hG := hG)) :
    DoubleBarrier.Enter.spec (GF := GF) (hG := hG) := by
  intro b s γ client id key count o lo
  wp_start as ⟨#Hb, Hmk, #Hlo⟩
  ihave #Hb' := Hb
  iunfold isDoubleBarrier at Hb'
  icases Hb' with ⟨#Hbs, #Hbctx, #Hbkey, #Hbcount, %Hcount, #Hsess, #Hcl, #Hclosed⟩
  ihave #Hcp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency $$ []
  · iPkgInit
  ihave Hci : (recipesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨-, -, ⟨%eT, #HeT⟩, -⟩
  have hpr : key ++ go!"/" <+: key ++ go!"/ready" := by
    rw [show go!"/ready" = go!"/" ++ go!"ready" from rfl, ← List.append_assoc]
    exact List.prefix_append _ _
  wp_auto
  wp_apply wp_Client s γ client id $$ [$Hcp $Hsess]
  (try wp_auto)
  wp_apply wp_enteredClients b s γ client id key count lo $$ [$Hb $Hlo] as %resp1 %err1 Hr1
  icases Hr1 with (⟨%Hnil1, %R1, %kvs1, #HR1, #Hw1, %HR1le⟩ | %Hne1)
  rotate_left
  · obtain ⟨e, rfl⟩ : ∃ e, err1 = GoInterface.ok e := by
      cases err1 with
      | nil => exact absurd rfl Hne1
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    unfold enterResult
    iright; iright
    isplitr
    · ipureintro; exact Hne1
    iexists o; iexact Hmk
  subst Hnil1
  iunfold waitersResp at Hw1
  icases Hw1 with ⟨%s1, %sl1, %ps1, #Hs1, %Hwf1, #Hsl1, #Hps1, #Hkv1, %Hp1⟩
  ihave %Hlen1 := ownSlice_len $$ Hps1
  wp_auto
  wp_if_destruct
  · iapply HΦ
    unfold enterResult
    iright; ileft
    isplitr
    · unfold concurrency.isPkgErr; iframe HeT; ipureintro; intro h; cases h
    iexists o; iexact Hmk
  have hpw : key ++ go!"/" <+: key ++ go!"/waiters" := by
    rw [show go!"/waiters" = go!"/" ++ go!"waiters" from rfl, ← List.append_assoc]
    exact List.prefix_append _ _
  wp_apply wp_newUniqueEphemeralKey s γ client id (key ++ go!"/") (key ++ go!"/waiters") lo
    $$ [$Hsess $Hcl $Hlo] as %ek %err Hres
  · ipureintro; exact hpw
  icases Hres with (⟨%Hnil, %kv, %k, %r, #HKVf, Hek, #Hr, #Hc, %Hkr⟩ | %Hne)
  rotate_left
  · obtain ⟨Hne, -⟩ := Hne
    obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    unfold enterResult
    iright; iright
    isplitr
    · ipureintro; exact Hne
    iexists o; iexact Hmk
  subst Hnil
  ihave #Hc' := Hc
  iunfold keyCreatedAt at Hc'
  icases Hc' with ⟨-, %sc, -, %Hcp⟩
  ihave ⟨%ek0, Hmk⟩ := dbMyKey_field b (key ++ go!"/") o $$ Hmk
  wp_auto
  ihave Hmk := dbMyKey_new b client (key ++ go!"/") (key ++ go!"/waiters") k kv ek r hpw Hkr.1
    $$ [$Hmk $Hek $HKVf $Hcl]
  wp_apply wp_enteredClients b s γ client id key count r $$ [$Hb $Hr] as %resp2 %err2 Hr2
  icases Hr2 with (⟨%Hnil2, %R2, %kvs2, #HR2, #Hw2, %HR2le⟩ | %Hne2)
  rotate_left
  · obtain ⟨e, rfl⟩ : ∃ e, err2 = GoInterface.ok e := by
      cases err2 with
      | nil => exact absurd rfl Hne2
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    unfold enterResult
    iright; iright
    isplitr
    · ipureintro; exact Hne2
    iexists _; iexact Hmk
  subst Hnil2
  iunfold waitersResp at Hw2
  icases Hw2 with ⟨%s2, %sl2, %ps2, #Hs2, %Hwf2, #Hsl2, #Hps2, #Hkv2, %Hp2⟩
  ihave %Hlen2 := ownSlice_len $$ Hps2
  iunfold kvPtrsAt at Hkv2
  icases Hkv2 with ⟨%Hpl2, #Hkv2⟩
  simp only [dbMyKey]
  icases Hmk with ⟨Hmk, Hek, #Hkv, %Hk⟩
  unfold ownEphemeralKV ownRemoteKV RemoteKVSt.val'
  wp_auto
  wp_if_destruct
  · -- at least `count` waiters: the `count`-th
    have Hc1 : 0 ≤ sint.Z (count - W64 1) ∧ sint.Z (count - W64 1) < sint.Z sl2.len := by
      constructor <;> word
    have Hi1 : sint.nat (count - W64 1) < ps2.length := by have := Hlen2.1; word
    have Hi2 : sint.nat (count - W64 1) < kvs2.length := by rw [← Hpl2]; exact Hi1
    obtain ⟨p, Hpi⟩ : ∃ p, ps2[sint.nat (count - W64 1)]? = some p :=
      ⟨_, List.getElem?_eq_getElem Hi1⟩
    obtain ⟨w, Hwi⟩ : ∃ w, kvs2[sint.nat (count - W64 1)]? = some w :=
      ⟨_, List.getElem?_eq_getElem Hi2⟩
    rw [ite_eq_left Hc1]
    icases ownSlice_elem_acc (sint.Z (count - W64 1)) p sl2 DFrac.discard ps2 Hc1.1
      (by exact Hpi) $$ Hps2 with ⟨#Hpe, -⟩
    ihave #Hwv := Hkv2 $$ %(sint.nat (count - W64 1)) %p %w %Hpi %Hwi
    iunfold kvValAt at Hwv
    icases Hwv with ⟨%wkeySl, %wvalSl, -, -, #Hwcr, -⟩
    wp_auto
    wp_if_destruct
    · -- too late: delete the key (its error ignored), `ErrTooManyClients`
      wp_method_call
      wp_auto
      wp_apply wp_Delete (structFieldRef EphemeralKV go!"RemoteKV" ek) ⟨GoInterface.ok kv, k, r, []⟩
        (key ++ go!"/") r $$ [Hek] as %derr ⟨Hek, -⟩
      · unfold ownRemoteKV RemoteKVSt.val'
        iframe Hek Hkv Hr
        ipureintro; exact Hk
      (try wp_auto)
      rcases derr with _ | _ <;> (try wp_auto) <;>
      · iapply HΦ
        unfold enterResult
        iright; ileft
        isplitr
        · unfold concurrency.isPkgErr; iframe HeT; ipureintro; intro h; cases h
        iexists none
        simp only [dbMyKey]
        iexists ek; iexact Hmk
    wp_if_destruct
    · -- the `count`-th: put `key/ready`
      ihave #Hkv' := Hkv
      iunfold isRecipesKV at Hkv'
      icases Hkv' with ⟨-, -, -, #HPut⟩
      iunfold isEtcdPutKVTodo at HPut
      ihave #Hnil : optsAt (GF := GF) slice.nil ([] : List (OpFull → OpFull)) $$ []
      · iapply concurrency.optsAt_nil
      ihave #HP := HPut $$ %(key ++ go!"/ready") %([] : GoString) %slice.nil
        %([] : List (OpFull → OpFull)) %(TxnOp.put (key ++ go!"/ready") [] (W64 0)) %R2
      wp_apply HP $$ [] as %presp %perr Hpres
      · iframe Hnil HR2
        ipureintro
        exact ⟨putOp_not_panics' _ _, putOp_txnOpOf' _ _, hpr⟩
      iunfold putResult at Hpres
      icases Hpres with (%Hpne | ⟨%Hpnil, -⟩)
      · obtain ⟨e, rfl⟩ : ∃ e, perr = GoInterface.ok e := by
          cases perr with
          | nil => exact absurd rfl Hpne
          | ok e => exact ⟨e, rfl⟩
        (try wp_auto)
        iapply HΦ
        unfold enterResult
        iright; iright
        isplitr
        · ipureintro; exact Hpne
        iexists none
        simp only [dbMyKey]
        iexists ek; iexact Hmk
      subst Hpnil
      (try wp_auto)
      iapply HΦ
      unfold enterResult
      ileft
      isplitr
      · ipureintro; rfl
      iexists ek, ⟨GoInterface.ok kv, k, _, []⟩
      simp only [dbMyKey]
      iframe Hmk Hc
      isplitl [Hek]
      · unfold ownEphemeralKV ownRemoteKV RemoteKVSt.val'; iframe Hek Hkv
        ipureintro; exact Hk
      isplitr
      · unfold enterReady
        ileft
        iexists R2
        iframe HR2
        unfold waitersSeen
        iexists s2
        iframe Hs2
        ipureintro
        unfold waiterCount
        rw [← Hp2.1.length_eq, ← Hpl2]
        have := Hlen2.1
        word
      ipureintro; exact ⟨Hkr.1, Hkr.2.1, fun h => by cases h⟩
    -- an earlier waiter: wait for `key/ready`
    (try wp_auto)
    wp_method_call
    wp_auto
    wp_apply wp_Revision (structFieldRef EphemeralKV go!"RemoteKV" ek) ⟨GoInterface.ok kv, k, r, []⟩
      $$ [Hek] as Hek
    · unfold ownRemoteKV RemoteKVSt.val'; iexact Hek
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %esl ⟨Hesl, -⟩
    ipersist Hesl
    wp_apply wp_WaitEvents client (key ++ go!"/") (key ++ go!"/ready") r _ [W32 0] (W32 0)
      $$ [$Hclosed $Hcl $Hesl] as %ev %werr ⟨%Hwnil, #Hev⟩
    · ipureintro; exact ⟨rfl, hpr, by word⟩
    subst Hwnil
    ihave ⟨%e, %v, %se, -, -, #Hre, #Hse, %Hve⟩ := waitedEvent_put _ _ _ _ $$ Hev
    obtain ⟨-, -, Hwk, Hwe⟩ := keyWatchOp_fields (key ++ go!"/ready") r
    (try wp_auto)
    iapply HΦ
    unfold enterResult
    ileft
    isplitr
    · ipureintro; rfl
    iexists ek, ⟨GoInterface.ok kv, k, r, []⟩
    simp only [dbMyKey]
    iframe Hmk Hc
    isplitl [Hek]
    · unfold ownEphemeralKV ownRemoteKV RemoteKVSt.val'; iframe Hek Hkv
      ipureintro; exact Hk
    isplitr
    · unfold enterReady
      iright
      iexists e.rev
      iframe Hre
      isplitr
      · unfold readyPut
        iexists se
        iframe Hse
        ipureintro
        obtain ⟨hv, -, hvk, hvm, -, hin⟩ := Hve
        rw [Hwk, Hwe] at hin
        refine ⟨v, hv, ?_, hvm⟩
        rw [hvk]; simpa [inRange] using hin
      ipureintro; exact Hve.2.2.2.2.1
    ipureintro; exact ⟨Hkr.1, Hkr.2.1, fun h => by cases h⟩
  -- fewer than `count` waiters: wait for `key/ready`
  (try wp_auto)
  wp_method_call
  wp_auto
  wp_apply wp_Revision (structFieldRef EphemeralKV go!"RemoteKV" ek) ⟨GoInterface.ok kv, k, r, []⟩
    $$ [Hek] as Hek
  · unfold ownRemoteKV RemoteKVSt.val'; iexact Hek
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %esl ⟨Hesl, -⟩
  ipersist Hesl
  wp_apply wp_WaitEvents client (key ++ go!"/") (key ++ go!"/ready") r _ [W32 0] (W32 0)
    $$ [$Hclosed $Hcl $Hesl] as %ev %werr ⟨%Hwnil, #Hev⟩
  · ipureintro; exact ⟨rfl, hpr, by word⟩
  subst Hwnil
  ihave ⟨%e, %v, %se, -, -, #Hre, #Hse, %Hve⟩ := waitedEvent_put _ _ _ _ $$ Hev
  obtain ⟨-, -, Hwk, Hwe⟩ := keyWatchOp_fields (key ++ go!"/ready") r
  (try wp_auto)
  iapply HΦ
  unfold enterResult
  ileft
  isplitr
  · ipureintro; rfl
  iexists ek, ⟨GoInterface.ok kv, k, r, []⟩
  simp only [dbMyKey]
  iframe Hmk Hc
  isplitl [Hek]
  · unfold ownEphemeralKV ownRemoteKV RemoteKVSt.val'; iframe Hek Hkv
    ipureintro; exact Hk
  isplitr
  · unfold enterReady
    iright
    iexists e.rev
    iframe Hre
    isplitr
    · unfold readyPut
      iexists se
      iframe Hse
      ipureintro
      obtain ⟨hv, -, hvk, hvm, -, hin⟩ := Hve
      rw [Hwk, Hwe] at hin
      refine ⟨v, hv, ?_, hvm⟩
      rw [hvk]; simpa [inRange] using hin
    ipureintro; exact Hve.2.2.2.2.1
  ipureintro; exact ⟨Hkr.1, Hkr.2.1, fun h => by cases h⟩

end proof

end recipes
end EtcdGrove
end Perennial
