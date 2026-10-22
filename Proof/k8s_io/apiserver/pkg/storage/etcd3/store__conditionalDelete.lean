/-
Lean-first (no Rocq counterpart).

The proof of `(*store).conditionalDelete`: the loop's invariant is the store's reading `s` of the
key's key-value at a state `σ` the caller's update fired at as a read (`rdOk`), with the caller's
token `W`. A missing key or a failed `validateDeletion` is the model's answer at `σ`
(`delete_none`, `delete_invalid`); `deleteOnce` either answers (an error, or the write) or, on a
conflict, gives the next iteration's reading.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__conditionalDelete
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getCurrentState
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__deleteOnce
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.refreshOnError

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.conditionalDelete.wp_proof
    (wp_getCur : store.getCurrentState.spec (GF := GF) (hG := hG))
    (wp_deleteOnce : store.deleteOnce.spec (GF := GF) (hG := hG))
    (wp_refresh : refreshOnError.spec (GF := GF) (hG := hG)) :
    store.conditionalDelete.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ E _ sp c ci cd key out o0 rv0 v p validate vf W Q Φu hk
  wp_start as ⟨#Hst, #Hctx, #Hce, Hout, %Hv, HW, #Hau, #Hval⟩
  ihave #Hrd := k8sAusRW_read c.ms c (delStep key validate) W Q Φu $$ Hau
  have hR : ∀ σ, rdOk (GF := GF) c Q σ ⊢ ⌜kvWf c σ⌝ := fun σ => by
    iintro #H
    iunfold rdOk at H
    icases H with ⟨-, %h, -⟩
    ipureintro; exact h.1
  (try wp_auto)
  wp_apply (wp_getCur Obj sp c ci cd go!"deleteGet" key v p (rdOk c Q) hk hR) $$ [] as %f #Hf
  · iframe #
    ipureintro; exact Hv
  (try wp_auto)
  iunfold getStateOk at Hf
  wp_apply Hf as %st %err Hr
  icases Hr with (#Herr | ⟨%σ, #Hrdσ, Hat⟩)
  · ihave %Hne := unkErr_ne c err $$ Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      (try wp_auto)
      iapply HΦ
      iunfold delOut
      ileft
      isplitr
      · iexact Herr
      iexists o0, rv0
      iexact Hout
  · unfold stAt
    cases hf : mvcc.findKey key σ.kvs with
    | none =>
      icases Hat with ⟨%Hst0, Herr⟩
      iunfold storageErrIs at Herr
      icases Herr with ⟨%ep, %Hep, #Hep⟩
      subst Hep
      (try wp_auto)
      iapply HΦ
      iunfold delOut
      iright
      iright
      iexists σ
      iunfold rdOk at Hrdσ
      icases Hrdσ with ⟨#HQ, %Hwf, -⟩
      rw [delete_none c σ key hf]
      iframe HQ HW
      isplitr
      · ipureintro; rfl
      simp only [respIs, storageErrIs]
      isplitl []
      · iexists ep
        iframe Hep
        ipureintro; rfl
      iexists o0, rv0
      iexact Hout
    | some kv =>
      icases Hat with ⟨%Herr, %s0, Hos, %Hs0⟩
      subst Herr
      (try wp_auto)
      ihave HI : (∃ (st : Loc) (s : OState Obj) (σ : KVState) (kv : EtcdKv) (e : GoInterface),
          "origState" ∷ origState_ptr ↦ st ∗ "err" ∷ err_ptr ↦ e ∗ "Hos" ∷ ownState c st s ∗
          "#Hrdσ" ∷ rdOk c Q σ ∗ "%Hkv" ∷ ⌜mvcc.findKey key σ.kvs = some kv ∧ stOfKv c kv s⌝ ∗
          "HW" ∷ W ∗ "Hout" ∷ c.S.objAt out o0 rv0 : IProp GF) $$ [origState err Hos HW Hout]
      · iexists st, s0, σ, kv, GoInterface.nil
        iframe origState err Hos HW Hout Hrdσ
        ipureintro; exact ⟨hf, Hs0⟩
      iclear Hrdσ
      clear hf Hs0 σ kv s0 st
      wp_for HI
      obtain ⟨hkv, hs⟩ := Hkv
      iunfold ownState at Hos
      icases Hos with ⟨%x, %m, %dsl, %Hstn, Hstp, Hobj, #Hdsl, Hm⟩
      (try wp_auto)
      iunfold validateOk at Hval
      wp_apply Hval $$ [$Hobj] as %verr Hobj %Hvres
      (try wp_auto)
      ihave Hos : ownState c st s $$ [Hstp Hobj Hm]
      · iunfold ownState
        iexists x, m, dsl
        iframe Hstp Hobj Hdsl Hm
        ipureintro; exact Hstn
      cases hvd : validate s.o (uint.nat s.rev) with
      | some e =>
        rw [hvd] at Hvres
        cases verr with
        | nil => exact absurd rfl Hvres.1
        | ok ei =>
          (try wp_auto)
          icases (ownState_split c st s) $$ Hos with ⟨%x', Hos, -⟩
          wp_apply wp_refresh Obj c st s (GoInterface.ok ei) f x' hs.2.2.2 $$ [$Hos]
            as %st' %err' ⟨%Heq, Hos⟩
          obtain ⟨rfl, rfl⟩ := Heq
          (try wp_auto)
          wp_for_post
          iapply HΦ
          iunfold delOut
          iright
          iright
          iexists σ
          ihave Hrd' := Hrdσ
          iunfold rdOk at Hrd'
          icases Hrd' with ⟨#HQ, %Hwf, -⟩
          rw [delete_invalid c σ key hk kv hkv s hs validate e hvd]
          iframe HQ HW
          isplitr
          · ipureintro; rfl
          simp only [respIs]
          isplitr
          · ipureintro; exact ⟨by nofun, Hvres.2⟩
          iexists o0, rv0
          iexact Hout
      | none =>
        rw [hvd] at Hvres
        subst Hvres
        (try wp_auto)
        wp_apply (wp_deleteOnce Obj E sp c ci cd key out o0 rv0 st s σ kv v p validate W Q Φu hk hkv
            hs hvd) $$ [$Hos $Hout $HW] as %st' %ok %derr Hd
        · iframe #
          ipureintro; exact Hv
        icases Hd with (⟨#Hde, Hout⟩ | ⟨%Hok, %σ', HΦu, Hresp⟩ | ⟨%Hok, HW, Hout, %σ', #Hrd', Hat⟩)
        · -- an error
          ihave %Hne := unkErr_ne c derr $$ Hde
          cases derr with
          | nil => exact absurd rfl Hne
          | ok ei =>
            (try wp_auto)
            wp_for_post
            iapply HΦ
            iunfold delOut
            ileft
            iframe Hout
            iexact Hde
        · -- deleted
          obtain ⟨rfl, rfl⟩ := Hok
          (try wp_auto)
          wp_for_post
          iapply HΦ
          iunfold delOut
          iright
          ileft
          iexists σ'
          iframe HΦu Hresp
        · -- a conflict
          subst Hok
          unfold stAt
          cases hf : mvcc.findKey key σ'.kvs with
          | none =>
            icases Hat with ⟨%Hst0, Herr⟩
            iunfold storageErrIs at Herr
            icases Herr with ⟨%ep, %Hep, #Hep⟩
            subst Hep
            (try wp_auto)
            wp_for_post
            iapply HΦ
            iunfold delOut
            iright
            iright
            iexists σ'
            ihave Hrd'' := Hrd'
            iunfold rdOk at Hrd''
            icases Hrd'' with ⟨#HQ, %Hwf, -⟩
            rw [delete_none c σ' key hf]
            iframe HQ HW
            isplitr
            · ipureintro; rfl
            simp only [respIs, storageErrIs]
            isplitl []
            · iexists ep
              iframe Hep
              ipureintro; rfl
            iexists o0, rv0
            iexact Hout
          | some kv' =>
            icases Hat with ⟨%Herr, %s', Hos', %Hs'⟩
            subst Herr
            (try wp_auto)
            wp_for_post
            iframe
            iexists st', s', σ', kv', GoInterface.nil
            iframe Hos' HW Hout Hrd'
            iframe
            ipureintro; exact ⟨hf, Hs'⟩

end proof

end k8s
end EtcdGrove
end Perennial
