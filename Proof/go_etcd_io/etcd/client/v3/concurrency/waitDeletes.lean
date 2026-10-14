/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/waitDeletes.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.waitDeletes
public import Spec.go_etcd_io.etcd.client.v3.concurrency.waitDelete
public import Spec.go_etcd_io.etcd.client.v3.WithLastCreate
public import Spec.go_etcd_io.etcd.client.v3.WithMaxCreateRev
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem waitDeletes.wp_proof (wp_WithLastCreate : WithLastCreate.spec (GF := GF) (hG := hG))
    (wp_WithMaxCreateRev : WithMaxCreateRev.spec (GF := GF) (hG := hG))
    (wp_waitDelete : waitDelete.spec (GF := GF) (hG := hG)) :
    waitDeletes.spec (GF := GF) (hG := hG) := by
  intro ctx cs client pfx maxCreateRev lo
  wp_start as ⟨#Hcl, #Hctx, #Hcc, #Hlo, %Hp⟩
  ihave #Hcl' := Hcl
  iunfold isEtcdMutexClient at Hcl'
  icases Hcl' with ⟨%kv, %wt, %cctx, %ccs, #Hkvf, -, -, -, #HKV, -, -, -⟩
  wp_auto
  wp_apply wp_WithLastCreate as %sl1 ⟨#Hsl1, Hcap1⟩
  wp_apply wp_WithMaxCreateRev maxCreateRev as %f #Hf
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
  ihave #Hopts : optsAt gsl (withTopM (W64 2) (W64 2) ++ [withMaxCreateRevM maxCreateRev]) $$ []
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
  ihave IH : iprop(∃ lo' : w64, "#Hlo'" ∷ etcdReached lo' ∗ "%Hlo'" ∷ ⌜sint.Z lo ≤ sint.Z lo'⌝) $$ []
  · iexists lo
    simp only [named]
    iframe Hlo
    ipureintro; exact Int.le_refl _
  wp_for IH
  (try wp_auto)
  iunfold isEtcdKV at HKV
  ihave #HG := HKV $$ %ctx %cs %pfx %gsl
    %(withTopM (W64 2) (W64 2) ++ [withMaxCreateRevM maxCreateRev]) %lo'
  wp_apply HG $$ [] as %gresp %gerr #Hgres
  · iframe Hctx Hopts Hlo'
    ipureintro
    exact ⟨lastCreateOp_not_panics maxCreateRev, lastCreateOp_t pfx maxCreateRev⟩
  iunfold kvGetResult at Hgres
  icases Hgres with (%Hgne | ⟨%Hgnil, %R, %gm, #HgRev, -, #HRR, %HRle, Hgr⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, gerr = GoInterface.ok e := by
      cases gerr with
      | nil => exact absurd rfl Hgne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    wp_for_post
    iapply HΦ
    ileft; ipureintro; exact Hgne
  subst Hgnil
  obtain ⟨Hrev0, Hser, HnP⟩ := lastCreateOp_rev pfx maxCreateRev
  have HRle' : sint.Z lo' ≤ sint.Z R := HRle.1 Hser
  have HnP' : (opGetModel pfx (withTopM (W64 2) (W64 2) ++ [withMaxCreateRevM maxCreateRev])).isPrefixGet
      pfx = false := HnP
  rw [ite_eq_right (c := (opGetModel pfx (withTopM (W64 2) (W64 2) ++
      [withMaxCreateRevM maxCreateRev])).isPrefixGet pfx = true) (by rw [HnP']; simp)]
  have Hunder := lastCreateOp_under pfx maxCreateRev Hp.1
  unfold getRespRange
  rw [ite_eq_left (show (opGetModel pfx (withTopM (W64 2) (W64 2) ++
      [withMaxCreateRevM maxCreateRev])).base.rev = W64 0 ∧
      KeyRangeUnder pfx (opGetModel pfx (withTopM (W64 2) (W64 2) ++
        [withMaxCreateRevM maxCreateRev])).key (opGetModel pfx (withTopM (W64 2) (W64 2) ++
        [withMaxCreateRevM maxCreateRev])).base.rangeEnd from ⟨Hrev0, Hunder⟩)]
  icases Hgr with ⟨%s', %gsl', %gps, %gkvs, #Hs', %Hwf', #Hgsl', #Hgps, #Hgkvs, %Hgok⟩
  obtain ⟨Hempty, Hmem⟩ := lastCreateOp_kvs pfx maxCreateRev s' gkvs Hp.1 Hwf' Hgok
  iunfold kvPtrsAt at Hgkvs
  icases Hgkvs with ⟨%Hgl, #Hgkv⟩
  ihave %Hgsl := ownSlice_len $$ Hgps
  wp_auto
  wp_if_destruct
  · -- nothing created at or before `maxCreateRev` is left
    have Hnil : gkvs = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← Hgl, Hgsl.1, Hif]; rfl
    (try wp_auto)
    wp_for_post
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iexists R, s'
    iframe HRR Hs'
    ipureintro
    exact ⟨by omega, Hempty Hnil⟩
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
  iunfold getRespRev at HgRev
  icases HgRev with ⟨%ghdr, #Hgh, %Hghnn, #HghR⟩
  ihave %Hrevs := etcdState_revs R pfx s' $$ Hs'
  wp_auto
  wp_apply wp_bytes_to_string keySl w.key DFrac.discard $$ [$HkeySl] as -
  have HR0 : 0 ≤ sint.Z R := by
    have := Hrevs w Hws
    omega
  wp_apply wp_waitDelete ctx cs client pfx w.key R $$ [$Hcl $Hctx $Hcc] as %werr Hwd
  · ipureintro; exact ⟨Hwf'.2 w Hws, HR0⟩
  icases Hwd with (%Hwne | ⟨%Hwnil, -⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, werr = GoInterface.ok e := by
      cases werr with
      | nil => exact absurd rfl Hwne
      | ok e => exact ⟨e, rfl⟩
    (try wp_auto)
    wp_for_post
    iapply HΦ
    ileft; ipureintro; exact Hwne
  subst Hwnil
  (try wp_auto)
  wp_for_post
  iframe
  iexists R
  simp only [named]
  iframe HRR
  ipureintro; omega

end proof

end concurrency
end EtcdGrove
end Perennial
