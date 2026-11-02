/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/leasekv/Main.lean` (the closed lease
example, 2026-11-02, `notes/lease-ex-plan.md`; as putget's). Lean-first (no Rocq counterpart).

The steps (Prove stage): `Main`'s premises in the shared start's form; the ghost state `NewServer`
takes (`common.alloc1`); `common.StartServer`; `go holdToken()` (`wp_fork_tok_self`: the goroutine never returns, its
token stays with `Main`); `common.Serve` with the ghost step `common.kv_lease_served` (the lease
reads registered at the address; the forked token goes into the one gRPC slot); `common.NewClient`; each
read's context with the request timeout (`client.wp_WithTimeout_bg`); `cli.Lease.Leases` (`Q`: the
IDs have no duplicate) and the double loop's check; `cli.Lease.TimeToLive(leaseID)` (`Q`: the reply's
ID is `7`) and its check. Every step's error ends `Main` (`return`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.leasekv.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.leasekv.holdToken
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.StartServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClient
public import Spec.go_etcd_io.etcd.client.v3.lessor__TimeToLive
public import Spec.go_etcd_io.etcd.client.v3.lessor__Leases
public import Perennial.Spec.context.Background
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.ServedLease
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasekv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.leasekv.Assumptions]

set_option maxHeartbeats 800000 in
/-- See the file header. -/
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_holdToken : holdToken.spec (GF := GF) (hG := hG))
    (wp_StartServer : common.StartServer.spec (GF := GF) (hG := hG))
    (wp_Serve : common.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : common.NewClient.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Leases : lessor.Leases.spec (GF := GF) (hG := hG))
    (wp_TimeToLive : lessor.TimeToLive.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC N id ctxs boot Hbf Htb Hrb48 HrbN Hck Haf Hbuq Hrf Hdbo HlP Hms hAs
  wp_start as ⟨Haddr, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hboot, #Hmarsh, #Hzap, #Hsetlg, #Htd, #Hns, #Htk, #Hnrl⟩
  -- `Main`'s premises in the shared start's form
  ihave #Hb := common.bootPremise_of N [id] (LogEntry.toEntries boot 0) ctxs (leasekvDir id)
      go!"leasekv" go!"leasekv"
      (common.urls1 go!"leasekv" go!"127.0.0.1:23946" go!"127.0.0.1:23936") id cfgOk urlsOk
      (fun _ h => by obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h; exact ⟨h1, by rw [h2]; rfl, h3, h4, h5, h6⟩)
      (fun _ h => by obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨h1, h2, h3, h4⟩) $$ Hboot
  ihave #Hcom : common.commonPremises (GF := GF) $$ []
  · iunfold common.commonPremises; iframe #
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg %Hlg
  (try wp_auto)
  -- the ghost state `NewServer` takes (`alloc1`)
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  imod (common.alloc1 id ctxs boot Hbf.idLow Hbf.boot Hbf.cc (leasekvDir id) (dirOne_member id _)
      (by omega) (by omega)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, -⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog⟩ := Hal
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- `StartServer("leasekv", peerAddr, clientAddr, lg)`
  have Hdirok : netDirOk (leasekvDir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  wp_apply (wp_StartServer N go!"leasekv" go!"127.0.0.1:23946" go!"127.0.0.1:23936" lg
      (LogEntry.toEntries boot 0) ctxs (leasekvDir id) id γ ρ E₀ Φs γn Htb Hrb48 HrbN hvs
      hrule hboot hblen hγn1 hγn2 Hdirok
      (by simp [leasekvDir, dirOne]) (by decide) Hlg Hck Haf Hbuq Hdbo) $$ [Htok Hmb]
    as %srv %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Hup⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  iunfold common.memberUp at Hup
  icases Hup with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, #Hwb, #Hsf,
    Hbemu, Hlts, Hlgs, Hrds, Hsts, Hbms, -, HWR, HLR⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  -- `go holdToken()`: the forked goroutine never returns; its token stays with `Main`
  ihave #Plk : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.leasekv $$ []
  · iPkgInit
  wp_apply wp_fork_tok_self as Htok2
  · wp_apply wp_holdToken as Hf
    iexfalso; iexact Hf
  (try wp_auto)
  -- `Serve(s, clientAddr)`, with etcd's KV calls and lease reads registered at the address; the
  -- forked goroutine's token goes into the one gRPC slot
  haveI := Hms
  wp_apply (wp_Serve srv go!"127.0.0.1:23936" E { ρ with wait := γw } ρ.rd cfg
      (fun _ _ _ => client.etcdLeaseReadAt (GF := GF) go!"127.0.0.1:23936")
      (by rw [HElg]; exact Hlg) HEtr HEw Hms Hbuq)
    $$ [Haddr Hlg3 Hbemu Hgo HWR Hlts Hlgs Hrds Hsts Hrslots Hbms HLR Htok2] as %serr Hs
  · iframe; iframe #
    iintro %gs %lis %cid %mid %R Hg
    imod (common.kv_lease_served srv E { ρ with wait := γw } ρ.rd gs lis go!"127.0.0.1:23936" cid
      mid R Hrb48 (by omega) Hrf HlP rfl) $$ [Hg Hlts Hlgs Hrds Hsts Hrslots Hbms HLR Htok2]
      with ⟨Htk, -, #Hlr⟩
    · unfold common.kvServeStocks
      iframe; iframe #
    imodintro; iframe; iframe #
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hlr⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hserr
  wp_auto
  iunfold client.etcdLeaseReadAt at Hlr
  icases Hlr with ⟨#Hrttl, #Hrls⟩
  -- `NewClient(clientAddr, lg)`
  wp_apply (wp_NewClient go!"127.0.0.1:23936" lg
      (EtcdGrove.client.srvWEnv R go!"127.0.0.1:23936" [] null null [] null default) Hlg
      (by unfold plainEndpoint; decide) (by omega)) as %cl %cerr Hcl
  icases Hcl with (⟨%Hcerr, #Hnc, -⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hcerr
  wp_auto
  iunfold isNewClient at Hnc
  icases Hnc with ⟨-, -, -, -, ⟨%lp, #Hlf, #Hla⟩, -⟩
  iunfold lessorAt at Hla
  icases Hla with ⟨%dc, %γd, %sc, %scd, %llg, %d, %γr, -, -, -, -, -, -, -, #Hrem, -, -⟩
  -- `lctx, lcancel := context.WithTimeout(context.Background(), common.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %lctx %lcd %lcancel ⟨#Hlcancel, #Hlctx, #Hlce, -⟩
  (try wp_auto)
  -- `cli.Lease.Leases(lctx)`, `Q`: the IDs have no duplicate
  wp_apply (wp_Leases lp [go!"127.0.0.1:23936"] etcdLeaseLeasesSpec
      (fun m => iprop(⌜m.ids.Nodup⌝)) lctx lcd) as %lsr %lerr Hls
  · iframe #
    imodintro; inext
    iunfold etcdLeaseLeasesSpec
    iintro %m %Hm
    ipureintro; exact Hm
  -- `lcancel()`
  (try wp_auto)
  wp_apply Hlcancel
  icases Hls with (⟨%Hlerr, %m, %h, %sl, #Hhf, -, #Hslf, Hsl, %Hnd⟩ | ⟨%Hlfail, -⟩)
  rotate_left
  · obtain ⟨Hlerr, -, -⟩ := Hlfail
    cases lerr with
    | nil => exact absurd rfl Hlerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
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
    have Hlt : sint.nat n < m.ids.length := by rw [List.length_map] at Hlen; word
    obtain ⟨x, hx⟩ : ∃ x, m.ids[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have hxs : (m.ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id)))[sint.nat n]? =
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
    · have Hlk : sint.nat k < m.ids.length := by word
      obtain ⟨y, hy⟩ : ∃ y, m.ids[sint.nat k]? = some y := ⟨_, List.getElem?_eq_getElem Hlk⟩
      have hys : (m.ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id)))[sint.nat k]? =
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
    -- `tctx, tcancel := context.WithTimeout(context.Background(), common.RequestTimeout)`
    wp_apply wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %tctx %tcd %tcancel ⟨#Htcancel, #Htctx, #Htce, -⟩
    (try wp_auto)
    -- `cli.Lease.TimeToLive(tctx, leaseID)`, `Q`: the reply's ID is `7`
    wp_apply (wp_TimeToLive lp [go!"127.0.0.1:23936"] etcdLeaseTTLSpec
        (fun m => iprop(⌜m.id = W64 7⌝)) tctx tcd (W64 7) slice.nil []) as %tr %terr Htl
    · iframe #
      isplitl
      · imodintro; inext
        iunfold etcdLeaseTTLSpec
        iintro %m %Hm
        ipureintro; exact Hm
      iunfold leaseOptsAt
      iexists ([] : List GoFunc)
      isplitl
      · iapply ownSlice_nil
      isplitl
      · ipureintro; rfl
      imodintro
      iintro %i %f %g %Hf %Hg
      simp at Hf
    -- `tcancel()`
    (try wp_auto)
    wp_apply Htcancel
    icases Htl with (⟨%Hterr, %mt, %ht, %ks, #Hth, -, #Htid, -, -, -, %Hmid⟩ | ⟨%Htfail, -⟩)
    rotate_left
    · obtain ⟨Hterr, -, -⟩ := Htfail
      cases terr with
      | nil => exact absurd rfl Hterr
      | ok ei => ?_
      wp_auto
      iapply HΦ; itrivial
    subst Hterr
    (try wp_auto)
    -- the check: the reply is about lease `7`
    simp only [Hmid, _root_.decide_true, Bool.not_true]
    wp_auto
    iapply HΦ; itrivial

end proof

end leasekv
end EtcdGrove
end Perennial
