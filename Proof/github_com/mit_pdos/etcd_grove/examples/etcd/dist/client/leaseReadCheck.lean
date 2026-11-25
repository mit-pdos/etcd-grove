/-
Proof of `leaseReadCheck.spec` (leaseN's `check` proof, `Proof/.../examples/etcd/leaseN/check.lean`, at a
member at another machine): `newClient([]string{addr})` (at any watch environment: the lease calls read none
of it); `defer cli.Close()`; `leaseList(cli)` (the draft `etcd_dist.Client_LeaseLeases_dist`: the IDs have no
duplicate) and leaseN's double loop; `cli.Lease.TimeToLive(tctx, 7)` (the draft
`etcd_dist.Client_LeaseTimeToLive_dist`: the reply's ID is `7`) and its check; at return, the deferred
`Close`. Every step's error returns `false`.
Lean-first (no Rocq counterpart); #50 N9b (`notes/etcd-dist-n9b.md`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.leaseReadCheck
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.leaseList
public import Spec.go_etcd_io.etcd.client.v3.Client__Close
public import Perennial.Spec.context.Background
public import Spec.context.WithTimeoutBackground
public import Spec.context.ErrAny
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist.view

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

set_option maxHeartbeats 1600000 in
/-- See the file header. -/
theorem leaseReadCheck.wp_proof (svc : DistView → w64 → GrpcSvc GF)
    (wp_newClient : newClient.spec (GF := GF) (hG := hG))
    (wp_leaseList : leaseList.spec (GF := GF) (hG := hG) svc)
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_TTL_dist : Client_LeaseTimeToLive_dist.spec (GF := GF) (hG := hG) svc)
    (wp_Close : EtcdGrove.Client.Close.spec (GF := GF) (hG := hG)) :
    leaseReadCheck.spec (GF := GF) (hG := hG) svc := by
  intro π Γ addr hV Htb hAs
  wp_start as ⟨Hlt, #Hm⟩
  iunfold leaseMember at Hm
  icases Hm with ⟨%Hok, %mid, #Haddr⟩
  have hpl : plainEndpoints [addr] := plainEndpoints_singleton _ (etcd_dist.addrOk_plainEndpoint Hok)
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  -- `newClient([]string{addr})`
  wp_apply wp_slice_literal (V := GoString) (l := [addr])
  isplitr
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  imod ownSlice_persist _ _ _ $$ Hlit with #Hlit
  (try wp_auto)
  wp_apply (wp_newClient _ [addr] (Classical.choice hV) Htb hpl) $$ [$Hlt] as %cl %cerr ⟨Hlt, Hcl⟩
  · iframe #
  icases Hcl with (⟨%Hcerr, #Hnc, #Hnp⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; iframe Hlt
  subst Hcerr
  ihave #Hcore := clientCoreAt_of_new cl [addr] (Classical.choice hV) $$ [Hnc Hnp]
  · iframe #
  ihave #Hmc : memberCli svc cl addr (Classical.choice hV) Γ mid $$ []
  · iunfold memberCli; iframe #
  icases leaseClientV_of_memberCli svc cl addr (Classical.choice hV) Γ mid $$ Hmc with ⟨%lp, #Hlc⟩
  (try wp_auto)
  -- `leaseList(cli)`: the IDs have no duplicate
  wp_apply (wp_leaseList cl addr (Classical.choice hV) Γ mid hAs) $$ [$Hlt] as %lsr %lerr ⟨Hlt, Hls⟩
  · iframe #
  icases Hls with (⟨%Hlerr, %ids, %sl, #Hslf, Hsl, %Hnd⟩ | %Hlfail)
  rotate_left
  · obtain ⟨Hlerr, -⟩ := Hlfail
    cases lerr with
    | nil => exact absurd rfl Hlerr
    | ok ei => ?_
    wp_auto
    wp_apply wp_Close as %ce -
    · iframe #
    (try wp_auto)
    iapply HΦ; iframe Hlt
  subst Hlerr
  (try wp_auto)
  -- the double loop: no ID twice (`Nodup`)
  imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
  ihave %Hlen := ownSlice_len $$ Hsl
  rename_i gi
  irename : (gi ↦ zero_val w64 : IProp GF) => gi
  ihave IO : (∃ (n gv : w64), "i" ∷ i_ptr ↦ n ∗ "gi" ∷ gi ↦ gv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n⌝ : IProp GF) $$ [i gi]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro; decide
  wp_for IO
  wp_if_destruct
  · -- the `n`th lease: none of the ones before it has its ID
    have Hlt : sint.nat n < ids.length := by rw [List.length_map] at Hlen; word
    obtain ⟨x, hx⟩ : ∃ x, ids[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have hxs : (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id)))[sint.nat n]? =
        some (go_etcd_io.etcd.client.v3.LeaseStatus.mk x) := by simp [hx]
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z n) _ DFrac.discard _ Hn $$ [Hsl] as -
    · iframe Hsl; ipureintro; exact hxs
    icases ownSlice_elem_acc (sint.Z n) _ sl DFrac.discard _ Hn hxs $$ Hsl with ⟨#Hxn, -⟩
    icases (go_etcd_io.etcd.client.v3.LeaseStatus.LeaseStatus_access_load_ID
        (sliceIndexRef go_etcd_io.etcd.client.v3.LeaseStatus (sint.Z n) sl)
        (go_etcd_io.etcd.client.v3.LeaseStatus.mk x) DFrac.discard).access_strict $$ Hxn with ⟨#Hxid, -⟩
    (try wp_auto)
    ihave IJ : (∃ (k : w64), "j" ∷ j_ptr ↦ k ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z n⌝ : IProp GF) $$ [j]
    · iexists W64 0
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    wp_for IJ
    wp_if_destruct
    · have Hlk : sint.nat k < ids.length := by word
      obtain ⟨y, hy⟩ : ∃ y, ids[sint.nat k]? = some y := ⟨_, List.getElem?_eq_getElem Hlk⟩
      have hys : (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id)))[sint.nat k]? =
          some (go_etcd_io.etcd.client.v3.LeaseStatus.mk y) := by simp [hy]
      icases ownSlice_elem_acc (sint.Z k) _ sl DFrac.discard _ Hk.1 hys $$ Hsl with ⟨#Hyk, -⟩
      icases (go_etcd_io.etcd.client.v3.LeaseStatus.LeaseStatus_access_load_ID
          (sliceIndexRef go_etcd_io.etcd.client.v3.LeaseStatus (sint.Z k) sl)
          (go_etcd_io.etcd.client.v3.LeaseStatus.mk y) DFrac.discard).access_strict $$ Hyk with ⟨#Hyid, -⟩
      have Hbk : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := ⟨Hk.1, by word⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      (try wp_auto)
      (try simp only [Hbk, _root_.and_self, ↓reduceIte])
      (try wp_auto)
      -- `k < n`: the IDs differ (`Nodup`)
      have Hne : x ≠ y := by
        intro hxy
        have := List.Nodup.eq_of_getElem?_eq (j := sint.nat k) Hnd Hlt (by rw [hx, hy, hxy])
        word
      rw [decide_eq_false Hne]
      (try wp_auto)
      wp_for_post
      iframe
      iexists k + W64 1
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    · (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, n
      simp only [named]
      iframe
      ipureintro; word
  · (try wp_auto)
    -- `tctx, tcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
    wp_apply wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %tctx %tcd %tcancel ⟨#Htcancel, #Htctx, #Htce, -⟩
    (try wp_auto)
    -- `cli.Lease.TimeToLive(tctx, leaseReadID)`: the reply's ID is `7`
    wp_apply (wp_TTL_dist cl lp addr (Classical.choice hV) Γ mid tctx tcd (W64 7)) $$ [$Hlt]
      as %tr %terr ⟨Hlt, Htl⟩
    · iframe #
    -- `tcancel()`
    (try wp_auto)
    wp_apply Htcancel
    icases Htl with (⟨%Hterr, #Htid⟩ | %Htfail)
    rotate_left
    · obtain ⟨Hterr, -⟩ := Htfail
      cases terr with
      | nil => exact absurd rfl Hterr
      | ok ei => ?_
      wp_auto
      wp_apply wp_Close as %ce -
      · iframe #
      (try wp_auto)
      iapply HΦ; iframe Hlt
    subst Hterr
    (try wp_auto)
    -- the check: the reply is about lease `7`
    (try simp only [_root_.decide_true, Bool.not_true])
    (try wp_auto)
    wp_apply wp_Close as %ce -
    · iframe #
    (try wp_auto)
    iapply HΦ; iframe Hlt

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
