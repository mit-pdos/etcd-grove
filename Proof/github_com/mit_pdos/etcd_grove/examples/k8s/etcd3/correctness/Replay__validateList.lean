/-
Lean-first (no Rocq counterpart).

The proof of `(*Replay).validateList`, on the accepting run: an error response, a consistent list,
or the list's resource version a state of the replay where `equalListResponse` accepts; the
rejecting branches contradict `rreplayListL R x out = true`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Replay__validateList
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ListReadConsistency
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__list
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__equalListResponse
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList__GetResourceVersion
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__ParseResourceVersion
public import Spec.k8s_io.apimachinery.pkg.api.meta.ListAccessor
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ListAccessorObjList

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Replay.validateList.wp_proof
    (wp_LRC : ListReadConsistency.spec (GF := GF) (hG := hG))
    (wp_list : Model.list.spec (GF := GF) (hG := hG))
    (wp_ELR : Model.equalListResponse.spec (GF := GF) (hG := hG))
    (wp_LA : apimeta.ListAccessor.spec (GF := GF) (hG := hG))
    (wp_GRV : k8s_etcd3.ObjList.GetResourceVersion.spec (GF := GF) (hG := hG))
    (wp_PRV : k8s_etcd3.versioner.ParseResourceVersion.spec (GF := GF) (hG := hG)) :
    Replay.validateList.spec (GF := GF) (hG := hG) := by
  intro rp R r ro x out hk hpre hlx hok
  wp_start as ⟨#HR, #Hreq, #Hresp⟩
  unfold replayAt
  icases HR with ⟨#Hdrv, %sm, %M, %csl, %cvs, #Hrp, #Hsm, %HMs, %HMrv, %HMch, #HMm, #Hcsl, #Hcvs⟩
  iStructNamed Hrp
  unfold reqRep
  rw [if_pos hk]
  icases Hreq with %Hreq
  obtain ⟨hop, hkey, hopts⟩ := Hreq
  ihave #Hresp0 := Hresp
  unfold respRep
  icases Hresp with ⟨#Ho, #He⟩
  ihave %Hen := errRep_nil_iff _ _ $$ He
  ihave %Hon := deepRep_nil_iff _ _ _ $$ Ho
  wp_auto
  cases hen : errNonNil out.err
  case true =>
    have hne : ro.Err' ≠ GoInterface.nil := fun h => by rw [Hen.1 h] at hen; cases hen
    obtain ⟨ii, hii⟩ : ∃ ii, ro.Err' = GoInterface.ok ii := by
      cases h : ro.Err' with
      | nil => exact absurd h hne
      | ok ii => exact ⟨ii, rfl⟩
    rw [hii]
    wp_auto
    iapply HΦ; ipureintro; rfl
  have he : ro.Err' = GoInterface.nil := Hen.2 hen
  rw [he]
  wp_auto
  obtain ⟨_, hparse, hlim, hflat, hlist, -⟩ := hpre
  rw [hopts]
  wp_apply (wp_LRC x hparse) $$ [] as %c %rv0 %ck %err %Hlrc
  · iframe #
  unfold rreplayListL at hok
  rw [hen] at hok
  simp only [Bool.false_eq_true, ↓reduceIte] at hok
  rcases hlc : listConsL x with _ | ⟨cs, r0⟩
  · rw [hlc] at hok; cases hok
  rw [hlc] at Hlrc hok
  obtain ⟨rfl, rfl, rfl, rfl⟩ := Hlrc
  wp_auto
  cases cs
  case consistent =>
    simp only [rconsStr, _root_.decide_true]
    wp_auto
    iapply HΦ; ipureintro; rfl
  all_goals simp only at hok
  all_goals
    simp (config := { decide := true }) only [rconsStr]
    wp_auto
    unfold deepRO
    cases ho : out.obj with
    | nil => rw [ho] at hok; cases hok
    | list items rv cont rem =>
      rw [ho] at hok
      simp only at hok
      iunfold deepRep at Ho
      icases Ho with ⟨%lp, %sl, %rlp, %hx, #Hl, -, -⟩
      rw [hx]
      wp_auto
      rw [hx]
      wp_apply (ListAccessor_objList wp_LA lp) as %acc %aerr %hacc
      obtain ⟨rfl, rfl⟩ := hacc
      wp_auto
      have hle1 : k8s_io.apimachinery.pkg.apis.«meta».v1.ListInterface.ty ≤u go.GoType.InterfaceType _ :=
        inferInstance
      have hle2 : go.UnderlyingDirectedEq k8s_io.apimachinery.pkg.api.«meta».List''.ty
        k8s_io.apimachinery.pkg.apis.«meta».v1.ListInterface.ty := inferInstance
      haveI : k8s_io.apimachinery.pkg.api.«meta».List''.ty ≤u go.GoType.InterfaceType _ :=
        ⟨hle2.underlying_unfold.trans hle1.underlying_eq⟩
      wp_auto
      wp_apply (wp_GRV lp DFrac.discard _) $$ [Hl]
      · iexact Hl
      iintro -
      simp only
      wp_auto
      wp_apply (wp_PRV (k8s_etcd3.rvStr rv)) as %n %perr Hpr
      rw [k8s_etcd3.parseRVD_rvStr]
      icases Hpr with %Hpr
      obtain ⟨rfl, rfl⟩ := Hpr
      wp_auto
      wp_apply (wp_map_lookup2 go.uint64
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty.PointerType sm M n
        DFrac.discard) $$ [Hsm] as -
      · iexact Hsm
      cases hst : R.states !! n with
      | none => rw [hst] at hok; cases hok
      | some st =>
        rw [hst] at hok
        obtain ⟨q, hq⟩ : ∃ q, M !! n = some q := by
          have := HMs n
          rw [hst] at this
          cases h : M !! n with
          | none => rw [h] at this; cases this
          | some q => exact ⟨q, rfl⟩
        ihave ⟨%m, %hm, #Hq⟩ := BigSepM.bigSepM_lookup (Φ := fun rv mp =>
          iprop(∃ m, ⌜R.states !! rv = some m⌝ ∗ modelAt (GF := GF) mp m)) hq $$ HMm
        rw [hst] at hm
        cases hm
        rw [hq]
        simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
        wp_auto
        rw [hkey, hopts]
        wp_apply (wp_list q st x hparse (hlim hk).1 (hlim hk).2) $$ [] as %re #Hre
        · iframe #
        (try wp_auto)
        rw [hkey, hopts]
        have hde : deepErrE (rlistL x st).err := hlx items n cont rem st ho hst
        wp_apply (wp_ELR q st x re ro (rlistL x st) out (rlistL_listOrNil x st) (hlist hk) hde hflat) $$ []
        · iframe #
          unfold respRep deepRO
          rw [hx, he, ho]
          iexact Hresp0
        simp only at hok
        rw [hok]
        wp_auto
        iapply HΦ; ipureintro; rfl
    | _ => rw [ho] at hok; cases hok

end proof

end k8s_correctness
end EtcdGrove
end Perennial
