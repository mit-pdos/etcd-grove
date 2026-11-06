/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/putget/Main.lean` (item 9, stage 2,
2026-10-18; over the examples' shared start since 2026-10-22, D33). Lean-first (no Rocq
counterpart).

The steps: `Main`'s premises in the shared start's form (`etcdstart.bootPremise_of`,
`commonPremises`); the ghost state `NewServer` takes (`etcdstart.alloc1`); `etcdstart.StartServer` (the member's configuration, `NewServer`, `Start`);
`etcdstart.Serve` (`v3rpc.Server`, `Listen`, `go gs.Serve(l)`) with the ghost step
`etcdstart.kv_served` (one gRPC slot; etcd's `Put` and `Range` registered at the address);
`etcdstart.NewClient` (`clientv3.New`); each call's context with the request timeout
(`context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`, `client.wp_WithTimeout_bg`:
an `isContext` whose `Err()` returns client errors, cancelled after the call; since 2026-10-23,
`notes/client-timeouts-plan.md`; `context.Background()` alone, quiet, until then); the client's
invariant at the bootstrap log (`putGetInv_alloc_log`); `cli.Put` (`client_Put_own`, its flag),
`cli.Get` (`client_Get_own`: the first key-value's value is `v`); the check, on the reply's message
(`rangeRespMsg`), takes the `else` branch. Every step's error ends `Main` (`return`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.putget.Main
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClient
public import Perennial.Spec.context.Background
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putget

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.putget.Assumptions]

set_option maxHeartbeats 800000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_StartServer : etcdstart.StartServer.spec (GF := GF) (hG := hG))
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : etcdstart.NewClient.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC N id ctxs boot Hbf Htb Hrb48 HrbN HwbN Hck Haf Hbuq Hrf Hdbo Hms hAs
  wp_start as ⟨Hstart, Htok, #Hprem⟩
  -- (hub step 7) the client address's listen right, out of the member's start bundle (to `Serve`)
  icases etcdstart.memberStartRes_client _ _ _ rfl $$ Hstart with ⟨Haddr, Hstart⟩
  iunfold premises at Hprem
  iunfold etcdstart.premises at Hprem
  icases Hprem with ⟨#Hboot, #Hmarsh, #Hzap, #Hsetlg, #Htd, #Hns, #Hnrl⟩
  -- `Main`'s premises in the shared start's form
  ihave #Hb := etcdstart.bootPremise_of N [id] (LogEntry.toEntries boot 0) ctxs (putgetDir id)
      go!"putget" go!"putget"
      (etcdstart.urls1 go!"putget" go!"127.0.0.1:23800" go!"127.0.0.1:23790") id cfgOk urlsOk
      (fun _ h => h)
      (fun _ h => h) $$ Hboot
  ihave #Hcom : etcdstart.commonPremises (GF := GF) $$ []
  · iunfold etcdstart.commonPremises; iframe #
  -- `context`'s `closedchan`, from its package's fact
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  -- the imports' package facts
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
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg %Hlg
  (try wp_auto)
  -- the ghost state `NewServer` takes (`alloc1`)
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  imod (etcdstart.alloc1_false id ctxs boot Hbf.idLow Hbf.boot Hbf.cc Hbf.urls (putgetDir id) (dirOne_member id _)
      (by omega) (by omega)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, Hetcd⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog⟩ := Hal
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- `StartServer("putget", "127.0.0.1:23800", clientAddr, lg)`
  -- (2026-10-24, rafthttp stage 6d) the one-member directory is well formed
  have Hdirok : netDirOk (putgetDir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  -- (hub step 7) no peer address: the start bundle is the fresh bundle at the network `γn`
  ihave Hfresh := etcdstart.memberStartRes_fresh _ _ γn rfl $$ Hstart
  wp_apply (wp_StartServer N go!"putget" go!"127.0.0.1:23800" go!"127.0.0.1:23790" lg
      (LogEntry.toEntries boot 0) ctxs (putgetDir id) id γ ρ E₀ Φs γn .none Htb Hrb48 HrbN HwbN hvs
      hrule hboot hblen hγn1 hγn2 Hdirok
      (by simp [putgetDir, etcdstart.dir1, dirOne]) (rafthttp.bootCfg_dirOne id _) (by decide) Hlg Hck Haf Hbuq Hdbo) $$ [Htok Hmb Hfresh]
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
    #Hsf, Hgo, Hlg3, Hbemu, HWR, ⟨Hlts, Hlgs, Hrds, Hsts, Hrslots, Hbms⟩, -, -⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  -- `Serve(s, clientAddr)`, with etcd's KV calls registered at the address
  haveI := Hms
  ihave ⟨%HsvOff, #HreqM, #HrdM, #Hlb⟩ := etcdstart.serveViews_off srv E { ρ with wait := γw } ρ.rd
    $$ []
  · iframe #
  wp_apply (wp_Serve srv go!"127.0.0.1:23790" E { ρ with wait := γw } ρ.rd cfg
      (fun cid mid _ => etcdstart.etcdKVAt go!"127.0.0.1:23790" E { ρ with wait := γw } ρ.rd cid mid))
    $$ [Haddr Hlg3 Hbemu Hgo HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr Hs
  · iframe; iframe #
    isplitr
    · ipureintro; exact ⟨by rw [HElg]; exact Hlg, HEtr, HEw, Hms, Hbuq, HsvOff.2⟩
    iintro %gs %lis %cid %mid %R Hg
    rw [HsvOff.1]
    ihave Hg := etcdstart.grpcUpM_false _ _ _ _ _ _ _ _ _ _ $$ Hg
    iapply (etcdstart.kv_served srv E { ρ with wait := γw } ρ.rd gs lis go!"127.0.0.1:23790" cid mid
      R Hrb48 Hrf rfl)
    unfold etcdstart.kvServeStocks
    iframe; iframe #
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hkv⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hserr
  wp_auto
  ihave #Hregs := etcdstart.etcdKVAt_regs go!"127.0.0.1:23790" E { ρ with wait := γw } ρ.rd cid mid
    rfl $$ Hkv
  -- `NewClient(clientAddr, lg)`
  wp_apply (wp_NewClient go!"127.0.0.1:23790" lg
      (EtcdGrove.client.srvWEnv R go!"127.0.0.1:23790" [] null null [] null default) Hlg
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
  -- `pctx, pcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %pctx %pcd %pcancel ⟨#Hpcancel, #Hpctx, #Hpce, -⟩
  (try wp_auto)
  -- the client's invariant, the floor, no options
  rw [kvModelSt_boot _ (fun _ _ => True) _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot)]
  imod (client.putGetInv_alloc_log ρ.rd (kvModel ρ.rd.kv (bootEntries (LogEntry.toEntries boot 0))) go!"k" go!"v" ⊤)
    $$ Hetcd with ⟨%γf, #Hinv⟩
  imod mvcc.idxCert_nil (GF := GF) E.γ.idx with #HF0
  ihave #Hnil : optsAt (GF := GF) slice.nil [] $$ []
  · iunfold optsAt
    iexists ([] : List GoFunc)
    isplitl
    · iapply ownSlice_nil
    isplitl
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    simp at Hf
  -- `cli.Put(ctx, "k", "v")`
  wp_apply (client.client_Put_own cl go!"127.0.0.1:23790" _ E ρ.rd γf cid mid
      pctx pcd go!"k" go!"v" slice.nil []
      (opSizeOk_opPutModel (K := 1) (E := 0) (V := 1) (optsKeep_nil _ _ _) (by decide) (by decide)
        (by decide))) as %presp %perr Hput
  · iframe #
  -- `pcancel()`
  (try wp_auto)
  wp_apply Hpcancel
  icases Hput with (⟨%Hperr, -, #Hflag⟩ | %Hpfail)
  rotate_left
  · obtain ⟨Hperr, -⟩ := Hpfail
    cases perr with
    | nil => exact absurd rfl Hperr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hperr
  (try wp_auto)
  -- `gctx, gcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -⟩
  (try wp_auto)
  -- `cli.Get(gctx, "k")`
  imod monoNatLbOwn_0 (GF := GF) ρ.rd.committed with #Hc0
  wp_apply (client.client_Get_own cl go!"127.0.0.1:23790" _ E ρ.rd γf (W64 0) cid mid
      gctx gcd go!"k" go!"v" slice.nil []
      (opSizeOk_opGetModel (K := 1) (E := 0) (V := 0) (optsKeep_nil _ _ _) (by decide) (by decide))) as %gresp %gerr Hget
  · iframe #
    iunfold committedAtLeast
    iExactEq Hc0; rfl
  -- `gcancel()`
  (try wp_auto)
  wp_apply Hgcancel
  icases Hget with (⟨%Hgerr, %m, #Hm, %Hv⟩ | %Hgfail)
  rotate_left
  · obtain ⟨Hgerr, -⟩ := Hgfail
    cases gerr with
    | nil => exact absurd rfl Hgerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hgerr
  (try wp_auto)
  iunfold rangeRespMsg at Hm
  icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hkvf, #Hsl, #Hkvs, #Hmore, #Hcount⟩
  -- the reply's first key-value holds `v`
  obtain ⟨kv0, Hkv0, Hval0⟩ : ∃ kv0, m.kvs[0]? = some kv0 ∧ kv0.value = go!"v" := by
    cases h : m.kvs with
    | nil => simp [h] at Hv
    | cons x xs => simp [h] at Hv; exact ⟨x, rfl, Hv⟩
  iunfold txn.kvsIs at Hkvs
  icases Hkvs with ⟨%Hlen, #Hall⟩
  obtain ⟨p0, Hp0⟩ : ∃ p0, ps[0]? = some p0 := by
    have : 0 < ps.length := by
      rw [Hlen]
      cases h : m.kvs with
      | nil => simp [h] at Hkv0
      | cons x xs => simp
    exact ⟨ps[0], List.getElem?_eq_getElem this⟩
  ihave #Hkv := Hall $$ %0 %p0 %kv0 %Hp0 %Hkv0
  iunfold txn.kvIs at Hkv
  icases Hkv with ⟨%kSl, %vSl, -, -, -, -, -, #HvF, #HvS, -⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have Hne : decide (sl.len = W64 0) = false := by
    rw [decide_eq_false_iff_not]
    intro h
    have hl := Hsll.1
    rw [h] at hl
    have : 0 < ps.length := List.length_pos_of_mem (List.mem_of_getElem? Hp0)
    rw [hl] at this
    exact absurd this (by decide)
  wp_auto
  simp only [Hne]
  wp_auto
  have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
    have := Hsll.1
    have : 0 < ps.length := List.length_pos_of_mem (List.mem_of_getElem? Hp0)
    constructor <;> word
  simp only [Hbnd, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd.1 $$ [Hsl] as -
  · iframe Hsl; ipureintro; exact Hp0
  wp_apply wp_bytes_to_string vSl kv0.value DFrac.discard $$ [HvS] as -
  · iframe #
  rw [Hval0]
  wp_auto
  iapply HΦ; itrivial

end proof

end etcd_putget
end EtcdGrove
end Perennial
