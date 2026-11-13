/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiry/Main.lean` (the closed
lease-expiry example, 2026-11-05, `notes/lease-expiry-plan.md`; as leasegrant's). Lean-first (no
Rocq counterpart).

The steps: `Main`'s premises in the shared start's form; the ghost state `NewServer` takes, at KV
names whose lessor is revocable (`etcdstart.alloc1` at the mode `.revocable`, with the open case
`srvRevokeOpen`); `etcdstart.StartServer`, whose post has the first start's
lease-TTL row (`leaseTTLRowR`); `go holdToken()`; `etcdstart.Serve` with
`etcdstart.kv_lease_served` at `.revocable` (the live grant, `TimeToLive` and `Leases` contracts
registered at the address); `etcdstart.NewClient`; `cli.Lease.Grant(1)` (`Q`: the lease live in
the lessor's history from an index, with its request `1`, `leaseReqIs`).
The poll loop keeps "`gone` → the lease absent from the history at an index at or after the
grant's": a `TimeToLive` answer `TTL = -1 ∧ GrantedTTL = 0` is, under the row (`leaseTTLRow`, from
`leaseTTLRowR` and the history's empty first snapshot), either the lease's recorded TTL `0` at a
later index, which `lease.leaseTTLAt_ge_req` refutes (the lease was requested at `1`), or its
absence. After the loop, `Leases()` is asked at the absence's index: the listing is a snapshot at
or after it, where the lease is still absent (`lease.lessorAt_absent_stays`: an id is granted once),
so the final loop finds nothing and does not panic. Every step's error ends `Main` (`return`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiry.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiry.holdToken
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClient
public import Spec.go_etcd_io.etcd.client.v3.lessor__Grant
public import Spec.go_etcd_io.etcd.client.v3.lessor__TimeToLive
public import Spec.go_etcd_io.etcd.client.v3.lessor__Leases
public import Perennial.Spec.context.Background
public import Perennial.Spec.time.Sleep
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.ServedLease
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorHist

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseexpiry

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiry.Assumptions]

-- the loop exits' `all_goals` simp sets: each lemma is used in some exit, not every one
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1600000 in
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
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG))
    (wp_Grant : lessor.Grant.spec (GF := GF) (hG := hG))
    (wp_TimeToLive : lessor.TimeToLive.spec (GF := GF) (hG := hG))
    (wp_Leases : lessor.Leases.spec (GF := GF) (hG := hG))
    -- the open case of `run`'s expiry arm (`srvRevokeOpen`): this example's names grant revocable
    -- leases (until the lease-expiry plan's S2–S4, also `srvGrantOpen`, a granting cluster's
    -- snapshot job)
    (hrev : srvRevokeOpen (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC N id ctxs boot Hbf Htb Hlev Hrb48 HrbN HwbN Hck Haf Hbuq Hrf Hdbo HlP Hms hAs
  wp_start as ⟨Hstart, Htok, #Hprem⟩
  -- (hub step 7) the client address's listen right, out of the member's start bundle (to `Serve`)
  icases etcdstart.memberStartRes_client _ _ _ rfl $$ Hstart with ⟨Haddr, Hstart⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hboot, #Hmarsh, #Hzap, #Hsetlg, #Htd, #Hns, #Hnrl⟩
  -- `Main`'s premises in the shared start's form
  ihave #Hb := etcdstart.bootPremise_of N [id] (LogEntry.toEntries boot 0) ctxs (leaseexpiryDir id)
      go!"leaseexpiry" go!"leaseexpiry"
      (etcdstart.urls1 go!"leaseexpiry" go!"127.0.0.1:23986" go!"127.0.0.1:23976") id cfgOk urlsOk
      (fun _ h => by obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h; exact ⟨h1, by rw [h2]; rfl, h3, h4, h5, h6⟩)
      (fun _ h => by obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨h1, h2, h3, h4⟩) $$ Hboot
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
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlgz
  (try wp_auto)
  -- the ghost state `NewServer` takes (`alloc1`), at KV names whose lessor is revocable
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  imod (etcdstart.alloc1 hne id ctxs boot Hbf.idLow Hbf.boot Hbf.cc Hbf.urls (leaseexpiryDir id)
      (dirOne_member id _) (by omega) (by omega) false 0 .revocable .revocable
      (lease.runCfg_revocable Hlev hrev)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, -⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, -, -, -, hlgρ⟩ := Hal
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- `StartServer("leaseexpiry", peerAddr, clientAddr, lg)`
  have Hdirok : netDirOk (leaseexpiryDir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  -- (hub step 7) no peer address: the start bundle is the fresh bundle at the network `γn`
  ihave Hfresh := etcdstart.memberStartRes_fresh _ _ γn rfl $$ Hstart
  wp_apply (wp_StartServer N go!"leaseexpiry" go!"127.0.0.1:23986" go!"127.0.0.1:23976" lg
      (LogEntry.toEntries boot 0) ctxs (leaseexpiryDir id) id γ ρ E₀ Φs γn .revocable Htb Hrb48
      HrbN HwbN hvs hrule hboot hblen hγn1 hγn2 Hdirok
      (by simp [leaseexpiryDir, dirOne]) (rafthttp.bootCfg_dirOne id _) (by decide) Hck Haf Hbuq
      Hdbo) $$ [Htok Hmb Hfresh]
    as %srv %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Hup, #Hrow⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  icases etcdstart.memberUp_served _ _ _ _ _ _ _ $$ Hup with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd,
    #Hsf, Hgo, Hlg3, Hbemu, HWR, ⟨Hlts, Hlgs, Hrds, Hsts, Hrslots, Hbms⟩, -, #HLR⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  -- the lessor's facts the argument uses: its reader invariant and its empty first snapshot, and
  -- the lease-TTL row of the first start
  ihave #HLR' := HLR
  iunfold etcdstart.srvLeaseRd at HLR'
  icases HLR' with ⟨%on, #Hsi⟩
  ihave #Hfirst := lease.srvInv_first on srv E .revocable $$ Hsi
  ihave #Hlrd := lease.srvInv_lessorRd on srv E .revocable $$ Hsi
  icases Hlrd with ⟨#Hslr, -⟩
  iunfold srvLessorRd at Hslr
  icases Hslr with ⟨%lpl, -, #Hlinv⟩
  iunfold lease.lessorInv at Hlinv
  icases Hlinv with ⟨-, -, -, #HrdInv⟩
  ihave #Hrow2 := leaseTTLRow_intro srv id (mvcc.api.mvccLeases E.γ) $$ [Hrow Hfirst]
  · iframe #
  -- `go holdToken()`: the forked goroutine never returns; its token stays with `Main`
  ihave #Plk : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiry $$ []
  · iPkgInit
  wp_apply wp_fork_tok_self as Htok2
  · wp_apply wp_holdToken as Hf
    iexfalso; iexact Hf
  (try wp_auto)
  -- `Serve(s, clientAddr)`, with the live grant, `TimeToLive` and `Leases` registered at the
  -- address; the forked goroutine's token goes into the one gRPC slot
  haveI := Hms
  have hlgw : ({ ρ with wait := γw } : ReqNames).rd.kv.lm = .revocable := hlgρ
  ihave ⟨%HsvOff, #HreqM, #HrdM, #Hlb⟩ := etcdstart.serveViews_off srv E { ρ with wait := γw } ρ.rd
    $$ []
  · iframe #
  wp_apply (wp_Serve srv go!"127.0.0.1:23976" E { ρ with wait := γw } ρ.rd cfg
      (fun _ _ _ => iprop(client.etcdLeaseReadAt (GF := GF) go!"127.0.0.1:23976" ∗
        etcdstart.etcdLeaseGrantLiveAt go!"127.0.0.1:23976" srv E ρ.rd)))
    $$ [Haddr Hlg3 Hbemu Hgo HWR Hlts Hlgs Hrds Hsts Hrslots Hbms Htok2] as %serr Hs
  · iframe; iframe #
    isplitr
    · ipureintro; exact ⟨by rw [HElg]; exact Hlg, HEtr, HEw, Hms, Hbuq, HsvOff.2⟩
    iintro %gs %lis %cid %mid %R Hg
    rw [HsvOff.1]
    ihave Hg := etcdstart.grpcUpM_false _ _ _ _ _ _ _ _ _ _ $$ Hg
    have h := etcdstart.kv_lease_served srv E { ρ with wait := γw } ρ.rd gs lis go!"127.0.0.1:23976"
      cid mid R Hrb48 (by omega) Hrf HlP rfl .revocable hlgw
    simp only [etcdstart.etcdLeaseServedAt] at h
    imod h $$ [Hg Hlts Hlgs Hrds Hsts Hrslots Hbms Htok2] with ⟨Htk, #Hlr, #Hga⟩
    · unfold etcdstart.kvServeStocks
      iframe; iframe #
    imodintro; iframe; iframe #
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hlr, #Hga⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hserr
  wp_auto
  iunfold etcdstart.etcdLeaseGrantLiveAt at Hga
  icases Hga with ⟨#Hrg, #Hrttl, #Hrls⟩
  -- `NewClient(clientAddr, lg)`
  wp_apply (wp_NewClient go!"127.0.0.1:23976" lg
      (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"127.0.0.1:23976" [] null null [] null default)
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
  -- `cli.Lease.Grant(gctx, grantTTL)`, `Q`: the lease live in the history from an index, its
  -- request `1`
  wp_apply (wp_Grant lp [go!"127.0.0.1:23976"]
      (etcdLeaseGrantSpecLive (EM := v3rpc.etcdModelOfServer E ρ.rd false) (mvcc.api.mvccLeases E.γ))
      (fun m => iprop(∃ (i : Nat) (l : Loc), lease.leaseLiveFrom (mvcc.api.mvccLeases E.γ) i m.id l ∗
        lease.leaseReqIs (mvcc.api.mvccLeases E.γ) m.id (W64 1))) gctx gcd) as %gr %gerr Hgr
  · iframe #
    imodintro; inext
    iunfold etcdLeaseGrantSpecLive
    iunfold etcdLeaseGrantSpecGR
    iunfold etcdLeaseGrantSpecG
    isplitr
    · ipureintro; rfl
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
  icases HQg with ⟨%gi, %gl, #Hlive, #Hgreq⟩
  ihave #Hlive' := Hlive
  iunfold lease.leaseLiveFrom at Hlive'
  icases Hlive' with ⟨%i0, %σg, %Hσg, #Hσat⟩
  ihave #Hlb0 := lease.lessorAt_lb (mvcc.api.mvccLeases E.γ) i0 σg $$ Hσat
  -- the poll loop: `gone` once the lease is found absent from the history after the grant
  ihave IO : (∃ (n : w64) (b : Bool), "i" ∷ i_ptr ↦ n ∗ "gone" ∷ gone_ptr ↦ b ∗
      "#Hb" ∷ (if b then lease.leaseAbsentFrom (GF := GF) (mvcc.api.mvccLeases E.γ) i0 mg.id else iprop(True)) :
      IProp GF) $$ [i gone]
  · iexists W64 0, false
    simp only [named, Bool.false_eq_true, ↓reduceIte]
    iframe
  wp_for IO
  wp_if_destruct
  -- `i < polls`: then `!gone`
  wp_if_destruct
  · -- one poll (`gone` false): `time.Sleep(pollEvery)`
    have hb : b = false := by revert Hif; cases b <;> simp [intoVal_eq_iff]
    subst hb
    wp_apply wp_Sleep
    (try wp_auto)
    -- `tctx, tcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
    wp_apply wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %tctx %tcd %tcancel ⟨#Htcancel, #Htctx, #Htce, -⟩
    (try wp_auto)
    -- `cli.Lease.TimeToLive(tctx, g.ID)` at the grant's index
    wp_apply (wp_TimeToLive lp [go!"127.0.0.1:23976"] (etcdLeaseTTLSpecLive (mvcc.api.mvccLeases E.γ) srv)
        (fun m => iprop(⌜m.id = mg.id⌝ ∗
          □ (leaseTTLRow srv (mvcc.api.mvccLeases E.γ) -∗
            (∃ i : Nat, ⌜i0 ≤ i⌝ ∗ lease.leaseTTLAt (mvcc.api.mvccLeases E.γ) i m.id m.grantedTtl) ∨
            lease.leaseAbsentFrom (mvcc.api.mvccLeases E.γ) i0 m.id)))
        tctx tcd mg.id slice.nil []) as %tr %terr Htl
    · iframe #
      isplitl
      · imodintro; inext
        iunfold etcdLeaseTTLSpecLive
        iexists i0
        iframe Hlb0
        iintro %m %Hm #Hm2
        isplitr
        · ipureintro; exact Hm
        iexact Hm2
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
    icases Htl with (⟨%Hterr, %mt, %ht, %ks, #Hth, -, #Htid, #Htttl, #Htg, -, %Hmid, #Hmt⟩ |
      ⟨%Htfail, -⟩)
    rotate_left
    · obtain ⟨Hterr, -, -⟩ := Htfail
      cases terr with
      | nil => exact absurd rfl Hterr
      | ok ei => ?_
      wp_auto
      wp_for_post
      iapply HΦ; itrivial
    subst Hterr
    -- the answer's case, under the row: its `GrantedTTL` is the lease's `ttl` (not `0`), or the
    -- lease is absent from the history after the grant
    ihave Hcase : iprop(|={⊤}=> (⌜mt.grantedTtl ≠ W64 0⌝ ∨
        lease.leaseAbsentFrom (mvcc.api.mvccLeases E.γ) i0 mg.id)) $$ []
    · ihave Hdis := Hmt $$ Hrow2
      icases Hdis with (⟨%j, %Hj, #Httl0⟩ | #Habs)
      · -- (the lease-expiry plan's S2–S4, Q-S8) every TTL of the lease at least its request, `1`
        imod lease.leaseTTLAt_ge_req (mvcc.api.mvccLeases E.γ) j mt.id (W64 1) mt.grantedTtl ⊤ (by simp)
          $$ [HrdInv Hgreq Httl0] with %Hge
        · rw [Hmid]; iframe #
        imodintro; ileft; ipureintro
        intro h0
        rw [h0] at Hge
        simp at Hge
      · imodintro; iright
        rw [← Hmid]
        iexact Habs
    imod Hcase with #Hcase
    (try wp_auto)
    wp_if_destruct
    · -- `TTL = -1`: then `GrantedTTL = 0`?
      (try wp_auto)
      wp_if_destruct
      · -- not found: the lease is absent from the history after the grant
        (try wp_auto)
        icases Hcase with (%Hne | #Habs)
        · exact absurd Hif Hne
        wp_for_post
        iframe
        iexists n + W64 1, true
        simp only [named, ite_true]
        iframe
        iexact Habs
      · (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, false
        simp only [named, Bool.false_eq_true, ↓reduceIte]
        iframe
    · (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, false
      simp only [named, Bool.false_eq_true, ↓reduceIte]
      iframe
  -- the loop is over (`i ≥ polls` or `gone`)
  all_goals
    cases b
    · -- not gone: `return` (or, the loop's condition true: impossible)
      first
        | (exfalso; revert Hif; simp [intoVal_eq_iff]; done)
        | ((try simp only [Bool.not_true, Bool.not_false, intoVal_eq_iff, Bool.true_eq_false, Bool.false_eq_true, decide_True_any, decide_False_any, decide_eq_self_any, ↓reduceIte])
           (try wp_auto)
           iapply HΦ; itrivial)
    -- gone: the absence's index
    (try simp only [Bool.not_true, Bool.not_false, intoVal_eq_iff, Bool.true_eq_false, Bool.false_eq_true, decide_True_any, decide_False_any, decide_eq_self_any, ↓reduceIte])
    (try wp_auto)
    (try simp only [↓reduceIte])
    iunfold lease.leaseAbsentFrom at Hb
    icases Hb with ⟨%k, %ρa, %Hρa, #Hρat⟩
    ihave #Hlbk := lease.lessorAt_lb (mvcc.api.mvccLeases E.γ) k ρa $$ Hρat
    -- `lctx, lcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
    wp_apply wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %lctx %lcd %lcancel ⟨#Hlcancel, #Hlctx, #Hlce, -⟩
    (try wp_auto)
    -- `cli.Lease.Leases(lctx)` at the absence's index: `Q`, a snapshot at or after it
    wp_apply (wp_Leases lp [go!"127.0.0.1:23976"] (etcdLeaseLeasesSpecLive (mvcc.api.mvccLeases E.γ))
        (fun m => iprop(∃ j : Nat, ⌜k ≤ j⌝ ∗ lease.leaseIdsAt (mvcc.api.mvccLeases E.γ) j m.ids)) lctx lcd)
        as %lsr %lerr Hls
    · iframe #
      imodintro; inext
      iunfold etcdLeaseLeasesSpecLive
      iexists k
      iframe Hlbk
      iintro %m Hm
      iexact Hm
    -- `lcancel()`
    (try wp_auto)
    wp_apply Hlcancel
    icases Hls with (⟨%Hlerr, %m, %h, %sl, #Hhf, -, #Hslf, Hsl, ⟨%j, %Hkj, #Hids⟩⟩ |
      ⟨%Hlfail, -⟩)
    rotate_left
    · obtain ⟨Hlerr, -, -⟩ := Hlfail
      cases lerr with
      | nil => exact absurd rfl Hlerr
      | ok ei => ?_
      wp_auto
      iapply HΦ; itrivial
    subst Hlerr
    (try wp_auto)
    -- the listing is a snapshot where the lease is still absent
    iunfold lease.leaseIdsAt at Hids
    icases Hids with ⟨%τ, %Hτ, #Hτat⟩
    imod lease.lessorAt_absent_stays (mvcc.api.mvccLeases E.γ) i0 k j σg ρa τ mg.id ⊤ (by simp)
        (by rw [Hσg.2]; rfl) Hρa.1 Hρa.2 Hkj $$ [HrdInv Hσat Hρat Hτat] with %Hτn
    · iframe #
    have Hnot : mg.id ∉ m.ids := by
      intro h
      have := (Hτ.2 mg.id).1 h
      rw [Hτn] at this
      simp at this
    -- the range loop: no element is the granted lease
    imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
    ihave %Hlen := ownSlice_len $$ Hsl
    rw [List.length_map] at Hlen
    rename_i gi'
    irename : (gi' ↦ zero_val w64 : IProp GF) => gi'
    ihave IR : (∃ (n gv : w64), "j" ∷ i_ptr ↦ n ∗ "gi" ∷ gi' ↦ gv ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n⌝ : IProp GF) $$ [i gi']
    · iexists W64 0, _
      simp only [named]
      iframe
      ipureintro; decide
    wp_for IR
    wp_if_destruct
    · have Hif' : sint.Z n < sint.Z sl.len := by simpa [intoVal_eq_iff] using Hif
      clear Hif
      have Hlt : sint.nat n < m.ids.length := by word
      obtain ⟨x, hx⟩ : ∃ x, m.ids[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
      have hxs : (m.ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id)))[sint.nat n]? =
          some (go_etcd_io.etcd.client.v3.LeaseStatus.mk x) := by simp [hx]
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn, Hif'⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z n) _ DFrac.discard _ Hn $$ [Hsl] as -
      · iframe Hsl; ipureintro; exact hxs
      icases ownSlice_elem_acc (sint.Z n) _ sl DFrac.discard _ Hn hxs $$ Hsl with ⟨#Hxn, -⟩
      icases (go_etcd_io.etcd.client.v3.LeaseStatus.LeaseStatus_access_load_ID
          (sliceIndexRef go_etcd_io.etcd.client.v3.LeaseStatus (sint.Z n) sl)
          (go_etcd_io.etcd.client.v3.LeaseStatus.mk x) DFrac.discard).access_strict $$ Hxn
        with ⟨#Hxid, -⟩
      (try wp_auto)
      (try simp only [Hbnd, _root_.and_self, ↓reduceIte])
      (try wp_auto)
      have hxg : x ≠ mg.id := by
        intro h; subst h; exact Hnot (List.mem_of_getElem? hx)
      rw [decide_eq_false hxg]
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, n
      simp only [named]
      iframe
      ipureintro; word
    · -- the end of the listing: no element was the granted lease
      (try wp_auto)
      (try simp only [decide_True_any, ↓reduceIte])
      (try wp_auto)
      iapply HΦ; itrivial

end proof

end etcd_leaseexpiry
end EtcdGrove
end Perennial
