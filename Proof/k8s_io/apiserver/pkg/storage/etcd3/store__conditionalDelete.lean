/-
Lean-first (no Rocq counterpart).

The proof of `(*store).conditionalDelete`: the first read goes through `rwInv` (D30n), which hands
the caller's token `W` at the first state with the response's pair where the model's step is the
identity; after it, the caller's result at a state with the response's answer, or `W` back
(`rwInv_after`). The loop's invariant is the store's reading `s` of the key's key-value at a state
`σ` the read fired at (`rdFacts`), with that result if `σ` hands, else `W`. A missing key or a
failed `validateDeletion` is the model's answer at `σ` (`delete_none`, `delete_invalid`, so `σ`
hands); `deleteOnce` either answers (an error, or the write) or, on a conflict, gives the next
iteration's reading, its update handed there if the step is the identity.
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
  intro _ _ Obj _ E _ sp c ci cd key out o0 rv0 v p validate vf W _ Φu hk
  wp_start as ⟨#Hst, #Hctx, #Hce, Hout, %Hv, HW, #Hau, #Hval⟩
  -- the first read's invariant, with the caller's token, and the maker `Get` takes
  imod (rwInv_alloc c key (stepHand c (delStep key validate)) W Φu ⊤) $$ HW
    with ⟨%γc, %γt, %γp, #Hrw, Htok, Hp⟩
  ihave Hmk := (rwInv_maker γc γt γp c key (delStep key validate)
    (stepHand c (delStep key validate)) (handOk_del c key validate) W Φu) $$ [Hp]
  · iframe Hrw Hp Hau
  have hR : ∀ R0 m σ, rdQ (GF := GF) γc γp c key (stepHand c (delStep key validate)) R0 m σ ⊢
      ⌜kvWf c σ⌝ := fun R0 m σ => by
    iintro #H
    iunfold rdQ at H
    icases H with ⟨#Hf, -, -⟩
    iunfold rdFacts at Hf
    icases Hf with ⟨%h, -⟩
    ipureintro; exact h.1
  wp_auto_lc 1
  wp_apply (wp_getCur Obj sp c ci cd go!"deleteGet" key v p
      (rdQ γc γp c key (stepHand c (delStep key validate))) hk hR) $$ [] as %f #Hf
  · iframe #
    ipureintro; exact Hv
  (try wp_auto)
  iunfold getStateOk at Hf
  wp_apply Hf $$ [Hmk] as %st %err Hr
  · iexact Hmk
  icases Hr with (#Herr | ⟨%σ, #Hrq, Hat⟩)
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
  · -- the response's state `σ`: the caller's result (if it hands) or the token back
    ihave #Hrq' := Hrq
    iunfold rdQ at Hrq'
    icases Hrq' with ⟨#Hfs, -, -⟩
    imod (rwInv_after γc γt γp c key (delStep key validate) (stepHand c (delStep key validate))
      (handOk_del c key validate) W Φu σ) $$ [Htok Hrq Hlc1] with HT
    · iframe Hrw Htok Hrq Hlc1
    unfold stAt
    cases hf : mvcc.findKey key σ.kvs with
    | none =>
      icases Hat with ⟨%Hst0, Herr⟩
      iunfold storageErrIs at Herr
      icases Herr with ⟨%ep, %Hep, #Hep⟩
      subst Hep
      have hid := delete_none c σ key hf (fun _ _ => none) validate
      have hh := hand_true c (delStep key validate) σ (by simp [delStep, hid])
      isimp only [hh, ↓reduceIte] at HT
      icases HT with ⟨%σ1, HΦ1, %Hsame⟩
      (try wp_auto)
      iapply HΦ
      iunfold delOut
      iright
      iexists σ1
      iframe HΦ1
      rw [delete_local key _ validate (c.abs σ1) (c.abs σ) Hsame.1 (by rw [abs_rv, abs_rv, Hsame.2]),
        hid]
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
          "#Hfs" ∷ rdFacts c σ ∗ "%Hkv" ∷ ⌜mvcc.findKey key σ.kvs = some kv ∧ stOfKv c kv s⌝ ∗
          "HT" ∷ (if stepHand c (delStep key validate) σ then iprop(∃ σ1, Φu σ1 ∗
            ⌜((c.abs σ1).delete key (fun _ _ => none) validate).2 =
              ((c.abs σ).delete key (fun _ _ => none) validate).2⌝) else W) ∗
          "Hout" ∷ c.S.objAt out o0 rv0 : IProp GF) $$ [origState err Hos HT Hout]
      · iexists st, s0, σ, kv, GoInterface.nil
        iframe origState err Hos Hout Hfs
        isplitr
        · ipureintro; exact ⟨hf, Hs0⟩
        cases hh : stepHand c (delStep key validate) σ
        · isimp only [hh, Bool.false_eq_true, ↓reduceIte] at HT
          simp only [Bool.false_eq_true, ↓reduceIte]
          iexact HT
        · isimp only [hh, ↓reduceIte] at HT
          simp only [↓reduceIte]
          icases HT with ⟨%σ1, HΦ1, %Hsame⟩
          iexists σ1
          iframe HΦ1
          ipureintro
          exact delete_local key _ validate (c.abs σ1) (c.abs σ) Hsame.1
            (by rw [abs_rv, abs_rv, Hsame.2])
      iclear Hfs Hrq
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
        have hinv := delete_invalid c σ key hk kv hkv s hs validate e hvd
        have hh := hand_true c (delStep key validate) σ (by simp [delStep, hinv])
        isimp only [hh, ↓reduceIte] at HT
        icases HT with ⟨%σ1, HΦ1, %Hans⟩
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
          iexists σ1
          iframe HΦ1
          rw [Hans, hinv]
          simp only [respIs]
          isplitr
          · ipureintro; exact ⟨by nofun, Hvres.2⟩
          iexists o0, rv0
          iexact Hout
      | none =>
        rw [hvd] at Hvres
        subst Hvres
        have hdel := delete_at c σ key hk kv kv hkv s hs rfl hs.1.symm validate hvd
        have hh := hand_false c (delStep key validate) σ (by simp only [delStep, hdel]; exact KSt.ne_of_rv)
        isimp only [hh, Bool.false_eq_true, ↓reduceIte] at HT
        (try wp_auto)
        wp_apply (wp_deleteOnce Obj E sp c ci cd key out o0 rv0 st s σ kv v p validate W Φu hk hkv
            hs hvd) $$ [$Hos $Hout $HT] as %st' %ok %derr Hd
        · iframe #
          ipureintro; exact Hv
        icases Hd with (⟨#Hde, Hout⟩ | ⟨%Hok, %σ', HΦu, Hresp⟩ | ⟨%Hok, Hout, %σ', #Hfs', Hat, HT'⟩)
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
            have hid := delete_none c σ' key hf (fun _ _ => none) validate
            have hh := hand_true c (delStep key validate) σ' (by simp [delStep, hid])
            isimp only [hh, ↓reduceIte] at HT'
            (try wp_auto)
            wp_for_post
            iapply HΦ
            iunfold delOut
            iright
            iexists σ'
            iframe HT'
            rw [hid]
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
            iframe Hos' Hout Hfs'
            iframe
            isplitr
            · ipureintro; exact ⟨hf, Hs'⟩
            cases hh : stepHand c (delStep key validate) σ'
            · isimp only [hh, Bool.false_eq_true, ↓reduceIte] at HT'
              simp only [Bool.false_eq_true, ↓reduceIte]
              iexact HT'
            · isimp only [hh, ↓reduceIte] at HT'
              simp only [↓reduceIte]
              iexists σ'
              iframe HT'
              ipureintro; rfl

end proof

end k8s
end EtcdGrove
end Perennial
