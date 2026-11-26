/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/foreign.lean`: each of the three calls
over its `Lease_*On_dist` contract at member `mid` (the context's metadata admitted for the client's principal,
`outTokOk_reqMd`). `Revoke`'s success is refuted by the caller's premise with `R`, so it errs and `refused`
returns; `TimeToLive`'s success returns keys each passing member `mid`'s read check (its post), so a returned key
equal to `forbidden` gives the check at `forbidden` (`leaseCheckD_wand`, the key's entry of the list), which the
caller refutes; `Leases`' result is ignored. Lean-first (no Rocq counterpart); F7 stage S5 (the single-process
`etcd_authlease.foreign.wp_proof`'s structure), the TimeToLive check F7 (fork).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.foreign
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.reqCtx
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.refused
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseRevokeOnDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseTimeToLiveOnDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseLeasesOnDist
public import Spec.go_etcd_io.etcd.client.v3.WithAttachedKeys
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthFrozenFloor
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist etcd_dist.authd

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- A lease check whose `K` implies `K'` is one with `K'`. -/
theorem leaseCheckD_wand (γa : auth.AuthNames) (P : Option GoString) (n : Nat)
    (K K' : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) :
    ⊢ □ (∀ info, K info -∗ K' info) -∗ leaseCheckD γa P n K -∗ leaseCheckD γa P n K' := by
  iintro #HK Hc
  iunfold leaseCheckD at Hc
  iunfold leaseCheckD
  icases Hc with (Hd | ⟨%info, %Hp, (Ha | Hk)⟩)
  · ileft; iexact Hd
  · iright; iexists info
    isplitr
    · ipureintro; exact Hp
    ileft; iexact Ha
  · iright; iexists info
    isplitr
    · ipureintro; exact Hp
    iright; iapply HK; iexact Hk

set_option maxHeartbeats 1600000 in
theorem foreign.wp_proof
    (wp_reqCtx : reqCtx.spec (GF := GF) (hG := hG))
    (wp_refused : refused.spec (GF := GF) (hG := hG))
    (wp_WithAttachedKeys : WithAttachedKeys.spec (GF := GF) (hG := hG))
    (wp_Revoke : Lease_RevokeOn_dist.spec (GF := GF) (hG := hG))
    (wp_TimeToLive : Lease_TimeToLiveOn_dist.spec (GF := GF) (hG := hG))
    (wp_Leases : Lease_LeasesOn_dist.spec (GF := GF) (hG := hG)) :
    foreign.spec (GF := GF) (hG := hG) := by
  intro π _ _ _ cl who addr id forbidden V Γ mid cfg γR L₀ n₀ m₀ Qr R Hau Hls Hauth Hrev HγR hP hAs
  wp_start as ⟨Hlt, #Hu, #Hat, #HL0, #Hn0, #Hm0, HR, #HQr, #HnoR, #HnoT⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave ⟨%lp, #Hlu⟩ := leaseUserAt_of_userCli cl addr V cfg Γ mid $$ [Hu Hat]
  · iframe #
  ihave #Hlu' := Hlu
  iunfold leaseUserAt at Hlu'
  icases Hlu' with ⟨#Hlc, -, %Htok⟩
  iunfold view.leaseClientAt at Hlc
  icases Hlc with ⟨-, -, #Hlf, -⟩
  have hout : outTokOk (principalOf cfg) (reqMd who) := outTokOk_reqMd _ who hP
  (try wp_auto)
  -- `Revoke(id)`
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply (wp_Revoke cl lp addr V Γ mid cfg γR L₀ n₀ ci cd (reqMd who) id Qr Hau Hauth Hrev HγR hout)
      $$ [$Hlt] as %r %err ⟨Hlt, Hr⟩
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hr with (⟨-, %mr, -, ⟨%σ, HQ⟩, #Hwc, -⟩ | %Herr)
  · iapply fupd_wp
    imod HnoR $$ %σ HQ Hwc HR with ⟨⟩
  wp_apply (wp_refused who _ err Herr.1)
  (try wp_auto)
  -- `TimeToLive(id, WithAttachedKeys())`
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply wp_WithAttachedKeys as %f #Hf
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f])
  isplitr
  · ipureintro; rfl
  iintro %slo ⟨Hslo, -⟩
  ipersist Hslo
  ihave #Hopts := leaseOptsAt_one_d (GF := GF) _ f (fun _ => true) $$ [Hslo Hf]
  · iframe #
  (try wp_auto)
  wp_apply (wp_TimeToLive cl lp addr V Γ mid cfg n₀ m₀ ci cd (reqMd who) id _ [fun _ => true] Hau Hls Hauth
      Hrev hout) $$ [$Hlt] as %r %err ⟨Hlt, Hr⟩
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  have hk : leaseKeysFold [fun _ => true] false = true := rfl
  icases Hr with (⟨%Herr, -, %n, %j, %Hnj, -, -, -, Hkeys⟩ | %Herr)
  · subst Herr
    try isimp only [hk, ↓reduceIte] at Hkeys
    icases Hkeys with ⟨%ks, %kbs, %kss, #Hksf, #Hks, #Hkbs, Hckk⟩
    ihave %Hkl := ownSlice_len $$ Hks
    ihave %Hkl2 := BigSepL2.bigSepL2_length $$ Hkbs
    (try wp_auto)
    ihave HI : (∃ (i : w64) (kb0 : GoSlice),
        "i" ∷ i_ptr ↦ i ∗ "kb" ∷ kb_ptr ↦ kb0 ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z ks.len⌝ : IProp GF) $$ [i kb]
    · iexists W64 0, _
      iframe
      ipureintro; constructor <;> word
    wp_for HI
    wp_if_destruct
    · have Hb' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z ks.len := ⟨Hi.1, Hif⟩
      simp only [Hb', _root_.and_self, ↓reduceIte]
      list_elem kbs (sint.nat i) as kb
      obtain ⟨k, hkv⟩ : ∃ k, kss[sint.nat i]? = some k :=
        ⟨_, List.getElem?_eq_getElem (by rw [← Hkl2]; exact (List.getElem?_eq_some_iff.1 Hkb_lookup).1)⟩
      wp_apply wp_load_slice_index ks (sint.Z i) kbs DFrac.discard kb Hi.1 $$ [Hks] as -
      · iframe #; ipureintro; exact Hkb_lookup
      ihave #Hkb := BigSepL2.bigSepL2_lookup Hkb_lookup hkv $$ Hkbs
      (try wp_auto)
      wp_apply wp_bytes_to_string kb k DFrac.discard $$ [Hkb] as -
      · iframe #
      (try wp_auto)
      wp_if_destruct
      · iapply fupd_wp
        ihave Hc := leaseCheckD_wand (Γ.au mid) (principalOf cfg) n _
          (fun info => auth.permVerdictFrom (.on (Γ.au mid)) n info forbidden [] .read GoInterface.nil) $$ [] Hckk
        · iintro !> %info Hl
          ihave H := BigSepL.bigSepL_lookup (Φ := fun _ k' =>
            auth.permVerdictFrom (GF := GF) (.on (Γ.au mid)) n info k' [] .read GoInterface.nil) hkv $$ Hl
          rw [← Hif]
          iexact H
        imod HnoT $$ %n %Hnj.1 Hc HR with ⟨⟩
      · (try wp_auto)
        wp_for_post
        iframe
        iexists i + W64 1, _
        iframe
        ipureintro
        constructor <;> word
    · (try wp_auto)
      -- `Leases()`, its result ignored
      wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout⟩
      subst Hc
      (try wp_auto)
      wp_apply (wp_Leases cl lp addr V Γ mid cfg n₀ m₀ ci cd (reqMd who) Hau Hls Hauth Hrev hout)
          $$ [$Hlt] as %r %err ⟨Hlt, -⟩
      · iframe #
      (try wp_auto)
      wp_apply Hcancel
      (try wp_auto)
      iapply HΦ; iframe Hlt HR
  cases err with
  | nil => exact absurd rfl Herr.1
  | ok ei =>
  (try wp_auto)
  -- `Leases()`, its result ignored
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply (wp_Leases cl lp addr V Γ mid cfg n₀ m₀ ci cd (reqMd who) Hau Hls Hauth Hrev hout)
      $$ [$Hlt] as %r %err ⟨Hlt, -⟩
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  iapply HΦ; iframe Hlt HR

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
