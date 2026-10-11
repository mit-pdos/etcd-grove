/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/RWMutex__waitOnLastRev.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.RWMutex__waitOnLastRev
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.RemoteKV__Revision
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.WaitEvents
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Client
public import Spec.go_etcd_io.etcd.client.v3.WithLastRev
public import Spec.go_etcd_io.etcd.client.v3.WithMaxModRev
public import Proof.go_etcd_io.etcd.client.v3.InvOpLemmas

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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem RWMutex.waitOnLastRev.wp_proof
    (wp_Client : concurrency.Session.Client.spec (GF := GF) (hG := hG))
    (wp_WithLastRev : WithLastRev.spec (GF := GF) (hG := hG))
    (wp_Revision : RemoteKV.Revision.spec (GF := GF) (hG := hG))
    (wp_WithMaxModRev : WithMaxModRev.spec (GF := GF) (hG := hG))
    (wp_WaitEvents : WaitEvents.spec (GF := GF) (hG := hG)) :
    RWMutex.waitOnLastRev.spec (GF := GF) (hG := hG) := by
  intro m s γ client id pfx bp ek st lo
  unfold rwMyKey
  wp_start as ⟨#Hm, ⟨Hmk, Hek, #Hkv, %Hk⟩, #Hlo, %Hp⟩
  ihave #Hm' := Hm
  iunfold isRWMutex at Hm'
  icases Hm' with ⟨#Hms, #Hmctx, #Hmpfx, %Hpfx, #Hsess, #Hcl, #Hclosed⟩
  ihave ⟨%kv, #HKVf, #Hkvc⟩ := isEtcdRecipesClient_kv client pfx $$ Hcl
  ihave #Hcp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Client s γ client id $$ [$Hcp $Hsess]
  (try wp_auto)
  wp_apply wp_WithLastRev as %sl1 ⟨#Hsl1, Hcap1⟩
  wp_method_call
  wp_auto
  unfold ownEphemeralKV
  wp_apply wp_Revision $$ [$Hek] as Hek
  wp_apply wp_WithMaxModRev (st.rev - W64 1) as %f #Hf
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  ipersist Hsl
  generalize hsl : slice.mk sl _ _ = litSl
  ihave #Hsl1' := Hsl1
  iunfold optsAt at Hsl1'
  icases Hsl1' with ⟨%fs1, #Hfs1, %Hlen1, #Hf1⟩
  wp_auto
  wp_apply wp_slice_append_persistent sl1 fs1 litSl [f] DFrac.discard $$ [$Hfs1 $Hcap1 $Hsl]
    as %gsl ⟨#Hgsl, -, -⟩
  ihave #Hopts : optsAt gsl (withTopM (W64 3) (W64 2) ++ [withMaxModRevM (st.rev - W64 1)]) $$ []
  · iunfold optsAt
    iexists fs1 ++ [f]
    iframe Hgsl
    isplitr
    · ipureintro; simp [Hlen1]
    imodintro
    iintro %i %f' %g %Hf' %Hg
    rcases Nat.lt_or_ge i fs1.length with h | h
    · rw [List.getElem?_append_left h] at Hf'
      rw [List.getElem?_append_left (by rw [← Hlen1]; exact h)] at Hg
      iapply Hf1 $$ %i %f' %g %Hf' %Hg
    · rw [List.getElem?_append_right h] at Hf'
      rw [List.getElem?_append_right (by rw [← Hlen1]; exact h)] at Hg
      rw [← Hlen1] at Hg
      rcases Nat.lt_or_ge (i - fs1.length) 1 with h' | h'
      · have h0 : i - fs1.length = 0 := by omega
        rw [h0] at Hf' Hg
        cases Hf'; cases Hg; iexact Hf
      · rw [List.getElem?_eq_none (by simp; omega)] at Hf'
        cases Hf'
  ihave #Hopts' := optsAt_res gsl _ iprop(True) $$ Hopts
  iunfold isRecipesKV at Hkvc
  icases Hkvc with ⟨#HKV, -, -, -⟩
  iunfold isEtcdKVTodo at HKV
  have hbp : bp ≠ [] := by
    intro h; subst h; exact Hpfx (List.prefix_nil.1 Hp.1)
  ihave #HG := HKV $$ %bp %gsl %(withTopM (W64 3) (W64 2) ++ [withMaxModRevM (st.rev - W64 1)])
    %iprop(True) %lo
  wp_apply HG $$ [] as %gresp %gerr ⟨-, #Hgres, -⟩
  · iframe Hopts' Hlo
    ipureintro
    exact ⟨lastRevOp_not_panics _, lastRevOp_t bp _⟩
  have Hop : opGetModel bp (withTopM (W64 3) (W64 2) ++ [withMaxModRevM (st.rev - W64 1)]) =
      lastRevOp bp (st.rev - W64 1) := rfl
  rw [Hop]
  iunfold kvGetResult at Hgres
  icases Hgres with (%Hgne | ⟨%Hgnil, %R, %gm, #HgRev, -, #HRR, %HRle, Hgr⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, gerr = GoInterface.ok e := by
      cases gerr with
      | nil => exact absurd rfl Hgne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    simp only
    iframe Hmk Hek Hkv
    isplitr
    · ipureintro; exact Hk
    iright; ipureintro; trivial
  subst Hgnil
  obtain ⟨Hrev0, Hser, HnP⟩ := lastRevOp_rev pfx bp (st.rev - W64 1)
  have HRle' : sint.Z lo ≤ sint.Z R := HRle.1 Hser
  rw [ite_eq_right (c := (lastRevOp bp (st.rev - W64 1)).isPrefixGet pfx = true) (by rw [HnP]; simp)]
  unfold getRespRange
  rw [ite_eq_left (show (lastRevOp bp (st.rev - W64 1)).base.rev = W64 0 ∧
      KeyRangeUnder pfx (lastRevOp bp (st.rev - W64 1)).key
        (lastRevOp bp (st.rev - W64 1)).base.rangeEnd from
    ⟨Hrev0, lastRevOp_under pfx bp _ hbp Hp.1⟩)]
  icases Hgr with ⟨%s', %gsl', %gps, %gkvs, #Hs', %Hwf', #Hgsl', #Hgps, #Hgkvs, %Hgok⟩
  obtain ⟨Hempty, Hmem⟩ := lastRevOp_kvs bp _ s' gkvs hbp Hgok
  iunfold kvPtrsAt at Hgkvs
  icases Hgkvs with ⟨%Hgl, #Hgkv⟩
  ihave %Hgsl := ownSlice_len $$ Hgps
  wp_auto
  wp_if_destruct
  · -- no blocking key: done
    have Hnil : gkvs = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← Hgl, Hgsl.1, Hif]; rfl
    (try wp_auto)
    iapply HΦ
    simp only
    iframe Hmk Hek Hkv
    isplitr
    · ipureintro; exact Hk
    ileft
    isplitr
    · ipureintro; simp
    iexists R, s'
    iframe HRR Hs'
    ipureintro
    refine ⟨HRle', fun v hv hvp => ?_⟩
    obtain ⟨hn0, hlt⟩ := Hempty Hnil v hv hvp
    have : sint.Z (st.rev - W64 1) = sint.Z st.rev - 1 := by word
    omega
  obtain ⟨kp, Hkp⟩ : ∃ kp, gps[0]? = some kp := by
    cases gps with
    | nil => exfalso; apply Hif; simp at Hgsl; word
    | cons kp _ => exact ⟨kp, rfl⟩
  obtain ⟨w, Hw⟩ : ∃ w, gkvs[0]? = some w := by
    cases gkvs with
    | nil => cases gps with
      | nil => cases Hkp
      | cons _ _ => simp at Hgl
    | cons w _ => exact ⟨w, rfl⟩
  have Hws : w ∈ s' := Hmem w (List.mem_of_getElem? Hw)
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z gsl'.len by
    constructor
    · word
    · have : gps.length ≠ 0 := by intro h; rw [List.length_eq_zero_iff] at h; subst h; cases Hkp
      have := Hgsl.1
      word)]
  icases ownSlice_elem_acc (sint.Z (W64 0)) kp gsl' DFrac.discard gps (by word) (by simpa using Hkp)
    $$ Hgps with ⟨#Hkpe, -⟩
  ihave #Hwv := Hgkv $$ %0 %kp %w %Hkp %Hw
  iunfold kvValAt at Hwv
  icases Hwv with ⟨%keySl, %valSl, #Hkey, #HkeySl, -⟩
  wp_auto
  wp_apply wp_bytes_to_string keySl w.key DFrac.discard $$ [$HkeySl] as -
  iclear HG HKV
  wp_method_call
  wp_auto
  wp_apply wp_Revision $$ [$Hek] as Hek
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %esl ⟨Hesl, -⟩
  ipersist Hesl
  wp_apply wp_WaitEvents client pfx w.key st.rev _ [W32 1] (W32 1) $$ [$Hclosed $Hcl $Hesl]
    as %ev %werr ⟨%Hwnil, -⟩
  · ipureintro; exact ⟨rfl, Hwf'.2 w Hws, by omega⟩
  subst Hwnil
  (try wp_auto)
  iapply HΦ
  simp only
  iframe Hmk Hek Hkv
  isplitr
  · ipureintro; exact Hk
  iright; ipureintro; trivial

end proof

end recipes
end EtcdGrove
end Perennial
