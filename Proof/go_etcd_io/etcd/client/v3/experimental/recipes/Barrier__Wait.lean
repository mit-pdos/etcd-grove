/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/Barrier__Wait.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.Barrier__Wait
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.WaitEvents
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas
public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3
open concurrency

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem Barrier.Wait.wp_proof (hWE : WaitEvents.spec (GF := GF) (hG := hG)) :
    Barrier.Wait.spec (GF := GF) (hG := hG) := by
  intro b client key lo
  wp_start as ⟨#Hcc, #Hb, #Hlo, %Hlo0⟩
  iunfold isBarrier at Hb
  icases Hb with ⟨#Hbc, #Hbx, #Hbk, #Hcl⟩
  ihave ⟨%kv, #Hkvf, #Hkv⟩ := isEtcdRecipesClient_kv $$ Hcl
  iunfold isRecipesKV at Hkv
  icases Hkv with ⟨#HGet, -, -, -⟩
  wp_auto
  ihave #Hnil := optsAt_nil (GF := GF)
  ihave #Hopts := optsAt_res slice.nil [] iprop(True) $$ Hnil
  iunfold isEtcdKVTodo at HGet
  ihave #HG := HGet $$ %key %slice.nil %([] : List (OpFull → OpFull)) %iprop(True) %lo
  wp_apply HG $$ [] as %gresp %gerr ⟨-, #Hgres, -⟩
  · iframe Hopts Hlo
    ipureintro
    exact ⟨keyOp_not_panics, (keyOp_t key).1⟩
  iunfold kvGetResult at Hgres
  icases Hgres with (%Hgne | ⟨%Hgnil, %R, %gm, #HgRev, -, #HRR, %HRle, Hgr⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, gerr = GoInterface.ok e := by
      cases gerr with
      | nil => exact absurd rfl Hgne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    iright
    ipureintro; exact Hgne
  subst Hgnil
  have HkT : (opGetModel key []).t = W64 1 ∧ (opGetModel key []).key = key ∧
      (opGetModel key []).base.rangeEnd = [] ∧ (opGetModel key []).base.rev = W64 0 ∧
      (opGetModel key []).base.serializable = false := keyOp_t key
  have HRle' : sint.Z lo ≤ sint.Z R := HRle.1 HkT.2.2.2.2
  have HkP : (opGetModel key []).isPrefixGet key = false := keyOp_isPrefixGet key key
  rw [ite_eq_right (c := (opGetModel key []).isPrefixGet key = true) (by rw [HkP]; simp)]
  unfold getRespRange
  rw [ite_eq_left (show (opGetModel key []).base.rev = W64 0 ∧
      KeyRangeUnder key (opGetModel key []).key (opGetModel key []).base.rangeEnd from
    ⟨HkT.2.2.2.1, by rw [HkT.2.1, HkT.2.2.1]; exact keyRangeUnder_key key key (List.prefix_refl key)⟩)]
  icases Hgr with ⟨%s', %gsl, %gps, %gkvs, #Hs', %Hwf', #Hgsl, #Hgps, #Hgkvs, %Hgok⟩
  iunfold kvPtrsAt at Hgkvs
  icases Hgkvs with ⟨%Hgl, -⟩
  ihave %Hgslen := ownSlice_len $$ Hgps
  obtain ⟨Hkabs, Hkpres⟩ := keyOp_kvs key key s' gkvs Hwf' Hgok
  wp_auto
  wp_if_destruct
  · -- no key: released already
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists R
    iframe HRR
    isplitl
    · unfold etcdAbsent
      iexists s'
      iframe Hs'
      ipureintro
      intro v hv hvk
      have h1 := Hkpres v hv hvk
      have h2 : gkvs.length = 0 := by rw [← Hgl]; word
      rw [h1] at h2; simp at h2
    ipureintro; exact HRle'
  · -- wait for the key's delete from `R + 1`
    iunfold getRespRev at HgRev
    icases HgRev with ⟨%hdr, #Hhdr, %Hhdrnn, #HhRev⟩
    wp_auto
    wp_apply wp_slice_literal (l := [evDelete])
    isplitr
    · ipureintro; rfl
    iintro %slT ⟨HslT, -⟩
    ipersist HslT
    (try wp_auto)
    wp_apply hWE client key key (R + W64 1) _ [evDelete] evDelete $$ [$Hpkg $Hcc $Hcl $HslT]
      as %ev %werr ⟨%Hwnil, #Hwev⟩
    · ipureintro
      refine ⟨rfl, List.prefix_refl key, ?_⟩
      have := HRle.2; word
    subst Hwnil
    ihave ⟨%r, #Hr, #Habs, %Hrr⟩ := waitedEvent_key_delete key key (R + W64 1) ev $$ Hwev
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists r
    iframe Hr Habs
    ipureintro
    have := HRle.2; word
