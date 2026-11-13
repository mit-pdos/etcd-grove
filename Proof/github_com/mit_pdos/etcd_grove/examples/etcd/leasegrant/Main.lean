/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leasegrant/Main.lean` (the closed
lease-grant example, 2026-11-02, `notes/lease-grant-plan.md`; as leasekv's). Lean-first (no Rocq
counterpart).

The steps (Prove stage): `Main`'s premises in the shared start's form; the ghost state `NewServer`
takes, at KV names that grant leases (`etcdstart.alloc1` at `lg = true`);
`etcdstart.StartServer`; `go holdToken()` (`wp_fork_tok_self`); `etcdstart.Serve` with the ghost step
`etcdstart.kv_lease_served` at `lg = true` (the lease reads and grants registered at the address);
`etcdstart.NewClient`; each call's context with the request timeout (`client.wp_WithTimeout_bg`);
`cli.Lease.Grant(600)` (at `etcdLeaseGrantSpec`: `Q` keeps the reply's lease granted at an index
of the lessor's history, `leaseGrantedAt`); `cli.Lease.Leases()` (at `etcdLeaseLeasesSpec`, handing
in `[g.ID]` with its grant: `Q`, the reply lists it) and the loop's check. Every step's error ends
`Main` (`return`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leasegrant.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leasegrant.holdToken
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClient
public import Spec.go_etcd_io.etcd.client.v3.lessor__Grant
public import Spec.go_etcd_io.etcd.client.v3.lessor__Leases
public import Perennial.Spec.context.Background
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.ServedLease
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leasegrant

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasegrant.Assumptions]

set_option maxHeartbeats 800000 in
/-- See the file header. -/
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_holdToken : holdToken.spec (GF := GF) (hG := hG))
    (wp_StartServer : etcdstart.StartServer.spec (GF := GF) (hG := hG))
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : etcdstart.NewClient.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Grant : lessor.Grant.spec (GF := GF) (hG := hG))
    (wp_Leases : lessor.Leases.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC N id ctxs boot Hbf Htb HLv Hrb48 HrbN HwbN Haf Hbuq Hrf Hdbo HlP HnE Hms hAs
  wp_start as ⟨Hstart, Htok, #Hprem⟩
  -- (hub step 7) the client address's listen right, out of the member's start bundle (to `Serve`)
  icases etcdstart.memberStartRes_client _ _ _ rfl $$ Hstart with ⟨Haddr, Hstart⟩
  iunfold premises at Hprem
  iunfold etcdstart.premises at Hprem
  icases Hprem with ⟨#Hboot, #Hmarsh, #Hzap, #Htd, #Hns, #Hnrl⟩
  -- `Main`'s premises in the shared start's form
  ihave #Hb := etcdstart.bootPremise_of N [id] (LogEntry.toEntries boot 0) ctxs (leasegrantDir id)
      go!"leasegrant" go!"leasegrant"
      (etcdstart.urls1 go!"leasegrant" go!"127.0.0.1:23966" go!"127.0.0.1:23956") id cfgOk urlsOk
      (fun _ h => h)
      (fun _ h => h) $$ Hboot
  ihave #Hcom : etcdstart.commonPremises (GF := GF) $$ []
  · iunfold etcdstart.commonPremises; iframe #
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
  wp_apply wp_NewNop as %lg #Hlgz
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlgz
  (try wp_auto)
  -- the ghost state `NewServer` takes (`alloc1`), at KV names that grant leases
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  imod (etcdstart.alloc1 hne id ctxs boot Hbf (leasegrantDir id)
      (dirOne_member id _) (by omega) (by omega) false 0 .mono .mono (lease.runCfg_mono HnE)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, -⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, -, -, -, hlgρ⟩ := Hal
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- `StartServer("leasegrant", peerAddr, clientAddr, lg)`
  have Hdirok : netDirOk (leasegrantDir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  -- (hub step 7) no peer address: the start bundle is the fresh bundle at the network `γn`
  ihave Hfresh := etcdstart.memberStartRes_fresh _ _ γn rfl $$ Hstart
  wp_apply (wp_StartServer N go!"leasegrant" go!"127.0.0.1:23966" go!"127.0.0.1:23956" lg
      (LogEntry.toEntries boot 0) ctxs (leasegrantDir id) id γ ρ E₀ Φs γn .mono Htb Hrb48 HrbN HwbN hvs
      hrule hboot hblen hγn1 hγn2 Hdirok
      (by simp [leasegrantDir, etcdstart.dir1, dirOne]) (rafthttp.bootCfg_dirOne id _) (by decide) Haf Hbuq Hdbo) $$ [Htok Hmb Hfresh]
    as %srv %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Hup, -⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  icases etcdstart.memberUp_served _ _ _ _ _ _ _ $$ Hup with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd,
    #Hsf, Hgo, Hlg3, Hbemu, #Hwb, Hstk, -, HLR⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  -- `go holdToken()`: the forked goroutine never returns (its token, which the gRPC runs needed
  -- until per-type stage B3, is no longer used: the runs borrow from the server's run pools)
  ihave #Plk : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leasegrant $$ []
  · iPkgInit
  wp_apply wp_fork_tok_self as -
  · wp_apply wp_holdToken as Hf
    iexfalso; iexact Hf
  (try wp_auto)
  -- `Serve(s, clientAddr)`, with the lease reads, the grant and the listing at the lessor's history
  -- registered at the address
  haveI := Hms
  have hlgw : ({ ρ with wait := γw } : ReqNames).rd.kv.lg = true := by
    show ρ.rd.kv.lg = true; rw [KVNames.lg_eq, hlgρ]; rfl
  ihave ⟨%HsvOff, #HreqM, #HrdM, #Hlb⟩ := etcdstart.serveViews_off srv E { ρ with wait := γw } ρ.rd
    $$ []
  · iframe #
  ihave #HzlgC : zapLoggerOk cfg.Logger' $$ []
  · rw [HElg]; iexact Hlgz
  wp_apply (wp_Serve srv go!"127.0.0.1:23956" E { ρ with wait := γw } ρ.rd cfg
      (fun _ _ _ => iprop(client.etcdLeaseReadAt (GF := GF) go!"127.0.0.1:23956" ∗
        etcdstart.etcdLeaseGrantAt go!"127.0.0.1:23956" E ρ.rd)))
    $$ [Haddr Hlg3 Hbemu Hgo Hstk HLR] as %serr Hs
  · iframe; iframe #
    isplitr
    · ipureintro; exact ⟨HEtr, HEw, Hms, Hbuq, HsvOff.2, Htb⟩
    iintro %gs %lis %cid %mid %R Hg
    rw [HsvOff.1]
    ihave Hg := etcdstart.grpcUpM_false _ _ _ _ _ _ _ _ _ _ $$ Hg
    have h := etcdstart.kv_lease_served srv E { ρ with wait := γw } ρ.rd gs lis go!"127.0.0.1:23956"
      cid mid R Hrb48 (by omega) Hrf HlP rfl .mono hlgρ HLv
    simp only [etcdstart.etcdLeaseServedAt] at h
    imod h $$ [Hg Hstk HLR] with ⟨Htk, #Hlr, #Hga⟩
    · iframe; iframe #
    imodintro; iframe; iframe #
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hlr, #Hga⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hserr
  wp_auto
  iunfold etcdstart.etcdLeaseGrantAt at Hga
  icases Hga with ⟨#Hrg, #Hrls⟩
  -- `NewClient(clientAddr, lg)`
  wp_apply (wp_NewClient go!"127.0.0.1:23956" lg
      (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"127.0.0.1:23956" [] null null [] null default)
      (by unfold plainEndpoint; decide) (by omega)) as %cl %cerr Hcl
  · iframe #
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
  -- `gctx, gcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -⟩
  (try wp_auto)
  -- `cli.Lease.Grant(gctx, grantTTL)`, `Q`: the reply's lease granted at an index of the history
  wp_apply (wp_Grant lp [go!"127.0.0.1:23956"]
      (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E ρ.rd false) (mvcc.api.mvccLeases E.γ))
      (fun m => iprop(∃ i : Nat, lease.leaseGrantedAt (mvcc.api.mvccLeases E.γ) i m.id)) gctx gcd) as %gr %gerr Hgr
  · iframe #
    imodintro; inext
    iunfold etcdLeaseGrantSpec
    iintro %m - - Hgi
    iexact Hgi
  -- `gcancel()`
  (try wp_auto)
  wp_apply Hgcancel
  icases Hgr with (⟨%Hgerr, %mg, %hg, #Hgh, -, #Hgid, -, #HQg⟩ | ⟨%Hgfail, -⟩)
  rotate_left
  · obtain ⟨Hgerr, -, -⟩ := Hgfail
    cases gerr with
    | nil => exact absurd rfl Hgerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hgerr
  (try wp_auto)
  -- `lctx, lcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %lctx %lcd %lcancel ⟨#Hlcancel, #Hlctx, #Hlce, -⟩
  (try wp_auto)
  -- `cli.Lease.Leases(lctx)`, handing in the grant: `Q`, the listing has the granted lease
  wp_apply (wp_Leases lp [go!"127.0.0.1:23956"] (etcdLeaseLeasesSpec (mvcc.api.mvccLeases E.γ))
      (fun m => iprop(⌜mg.id ∈ m.ids⌝)) lctx lcd) as %lsr %lerr Hls
  · iframe #
    imodintro; inext
    iunfold etcdLeaseLeasesSpec
    iexists [mg.id]
    isplitl
    · iapply BigSepL.bigSepL_cons.2
      iframe HQg
      iapply BigSepL.bigSepL_nil.2
      itrivial
    iintro %m %Hm
    ipureintro; exact Hm.2 mg.id (List.mem_singleton_self _)
  -- `lcancel()`
  (try wp_auto)
  wp_apply Hlcancel
  icases Hls with (⟨%Hlerr, %m, %h, %sl, #Hhf, -, #Hslf, Hsl, %Hin⟩ | ⟨%Hlfail, -⟩)
  rotate_left
  · obtain ⟨Hlerr, -, -⟩ := Hlfail
    cases lerr with
    | nil => exact absurd rfl Hlerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hlerr
  (try wp_auto)
  -- the loop: `found` once the granted lease is met
  imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
  ihave %Hlen := ownSlice_len $$ Hsl
  rw [List.length_map] at Hlen
  rename_i gi
  irename : (gi ↦ zero_val w64 : IProp GF) => gi
  ihave IO : (∃ (n gv : w64) (b : Bool), "i" ∷ i_ptr ↦ n ∗ "gi" ∷ gi ↦ gv ∗
      "found" ∷ found_ptr ↦ b ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ (b = true ∨ mg.id ∉ m.ids.take (sint.nat n))⌝ : IProp GF)
      $$ [i gi found]
  · iexists W64 0, _, false
    simp only [named]
    iframe
    ipureintro
    refine ⟨by decide, Or.inr ?_⟩
    rw [show sint.nat (W64 0) = 0 by rfl]
    simp
  clear hlgw
  wp_for IO
  wp_if_destruct
  · -- the `n`th lease
    have Hif' : sint.Z n < sint.Z sl.len := by simpa using Hif
    clear Hif
    have Hlt : sint.nat n < m.ids.length := by word
    obtain ⟨x, hx⟩ : ∃ x, m.ids[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have hxs : (m.ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id)))[sint.nat n]? =
        some (go_etcd_io.etcd.client.v3.LeaseStatus.mk x) := by simp [hx]
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif'⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z n) _ DFrac.discard _ Hn.1 $$ [Hsl] as -
    · iframe Hsl; ipureintro; exact hxs
    icases ownSlice_elem_acc (sint.Z n) _ sl DFrac.discard _ Hn.1 hxs $$ Hsl with ⟨#Hxn, -⟩
    icases (go_etcd_io.etcd.client.v3.LeaseStatus.LeaseStatus_access_load_ID
        (sliceIndexRef go_etcd_io.etcd.client.v3.LeaseStatus (sint.Z n) sl)
        (go_etcd_io.etcd.client.v3.LeaseStatus.mk x) DFrac.discard).access_strict $$ Hxn
      with ⟨#Hxid, -⟩
    (try wp_auto)
    (try simp only [Hbnd, _root_.and_self, ↓reduceIte])
    (try wp_auto)
    have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    by_cases hxg : x = mg.id
    · rw [decide_eq_true hxg]
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, n, true
      simp only [named]
      iframe
      ipureintro
      exact ⟨by word, by simp⟩
    · rw [decide_eq_false hxg]
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, n, b
      simp only [named]
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      rcases Hn.2 with hb | hnot
      · exact Or.inl hb
      · right
        rw [hsn, List.take_add_one, hx]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
        exact ⟨hnot, fun h => hxg h.symm⟩
  · -- the listing has the granted lease: `found`
    have hb : b = true := by
      rcases Hn.2 with hb | hnot
      · exact hb
      · exfalso
        apply hnot
        rw [List.take_of_length_le (by word)]
        exact Hin
    subst hb
    (try wp_auto)
    iapply HΦ; itrivial

end proof

end etcd_leasegrant
end EtcdGrove
end Perennial
