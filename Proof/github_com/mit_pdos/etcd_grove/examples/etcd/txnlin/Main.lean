/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/txnlin/Main.lean` (over the examples' shared
start since 2026-10-22, D33). Lean-first (no Rocq counterpart).

The server's start is putget's `Main`'s (`Proof/.../putget/Main.lean`), at `linkvtxn`'s
configuration: `Main`'s premises in the shared start's form (`etcdstart.bootPremise_of`); the ghost
state `NewServer` takes (`etcdstart.alloc1`);
`etcdstart.StartServer`; `etcdstart.Serve` with the ghost step `etcdstart.grpcUp_noRefusal` (the member
refusal-free, D29) then `etcdstart.kv_served` (etcd's KV calls registered at the address);
`etcdstart.NewClient` (etcd's default configuration; `clientWriteOnce`, D29). Then the instance's
invariant at the server's start store (`linkvInv_alloc_boot`: the bootstrap log changes no KV
state) and `Check(cli, clients, ops, 0)`, which returns `Ok` (`timeout = 0`), so the panic on
`Illegal` is not taken. Every step's error ends `Main` with `Unknown`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Check
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Boot
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]

set_option maxHeartbeats 800000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_StartServer : etcdstart.StartServer.spec (GF := GF) (hG := hG))
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : etcdstart.NewClient.spec (GF := GF) (hG := hG))
    (wp_Check : Check.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC N id ctxs boot clients ops Hbf Htb Hrb48 HrbN HwbN Hck Haf Hbuq Hrf Hdbo Hms hAs
    H0 H31 Hops Hmul
  wp_start as ⟨Hstart, Htok, #Hprem⟩
  -- (hub step 7) the client address's listen right, out of the member's start bundle (to `Serve`)
  icases etcdstart.memberStartRes_client _ _ _ rfl $$ Hstart with ⟨Haddr, Hstart⟩
  iunfold premises at Hprem
  iunfold etcdstart.premises at Hprem
  icases Hprem with ⟨#Hboot, #Hmarsh, #Hzap, #Hsetlg, #Htd, #Hns, #Hnrl⟩
  -- `Main`'s premises in the shared start's form
  ihave #Hb := etcdstart.bootPremise_of N [id] (LogEntry.toEntries boot 0) ctxs (linkvtxnDir id) go!"linkvtxn" go!"linkvtxn"
      (etcdstart.urls1 go!"linkvtxn" go!"127.0.0.1:23806" go!"127.0.0.1:23796") id cfgOk urlsOk
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
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlgz
  (try wp_auto)
  -- the ghost state `NewServer` takes (`alloc1`)
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  imod (etcdstart.alloc1_false id ctxs boot Hbf.idLow Hbf.boot Hbf.cc Hbf.urls (linkvtxnDir id) (dirOne_member id _)
      (by omega) (by omega)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, Hetcd⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog, -⟩ := Hal
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- `StartServer("linkvtxn", "127.0.0.1:23806", clientAddr, lg)`
  -- (2026-10-24, rafthttp stage 6d) the one-member directory is well formed
  have Hdirok : netDirOk (linkvtxnDir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  -- (hub step 7) no peer address: the start bundle is the fresh bundle at the network `γn`
  ihave Hfresh := etcdstart.memberStartRes_fresh _ _ γn rfl $$ Hstart
  wp_apply (wp_StartServer N go!"linkvtxn" go!"127.0.0.1:23806" go!"127.0.0.1:23796" lg (LogEntry.toEntries boot 0) ctxs
      (linkvtxnDir id) id γ ρ E₀ Φs γn .none Htb Hrb48 HrbN HwbN hvs
      hrule hboot hblen hγn1 hγn2 Hdirok
      (by simp [linkvtxnDir, etcdstart.dir1, dirOne]) (rafthttp.bootCfg_dirOne id _) (by decide) Hck Haf Hbuq Hdbo) $$ [Htok Hmb Hfresh]
    as %srv %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Hup, -⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    simp only [github_com.anishathalye.porcupine.Unknown]
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Herr
  wp_auto
  icases etcdstart.memberUp_served _ _ _ _ _ _ _ $$ Hup with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd,
    #Hsf, Hgo, Hlg3, Hbemu, HWR, ⟨Hlts, Hlgs, Hrds, Hsts, Hrslots, Hbms⟩, -, -⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  -- `Serve(s, clientAddr)`: (D29) the member never refuses (authentication off, a voter, the
  -- members' axiom), and etcd's KV calls registered at the address
  haveI := Hms
  ihave ⟨%HsvOff, #HreqM, #HrdM, #Hlb⟩ := etcdstart.serveViews_off srv E { ρ with wait := γw } ρ.rd
    $$ []
  · iframe #
  wp_apply (wp_Serve srv go!"127.0.0.1:23796" E { ρ with wait := γw } ρ.rd cfg
      (fun cid mid _ => iprop(etcdstart.etcdKVAt go!"127.0.0.1:23796" E { ρ with wait := γw } ρ.rd cid mid ∗
        ⌜noRefusalAt go!"127.0.0.1:23796"⌝)))
    $$ [Haddr Hlg3 Hbemu Hgo HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr Hs
  · iframe; iframe #
    isplitr
    · ipureintro; exact ⟨by rw [HElg]; exact Hlg, HEtr, HEw, Hms, Hbuq, HsvOff.2⟩
    iintro %gs %lis %cid %mid %R Hg
    rw [HsvOff.1]
    ihave Hg := etcdstart.grpcUpM_false _ _ _ _ _ _ _ _ _ _ $$ Hg
    ihave ⟨Hg, %Hnr⟩ := etcdstart.grpcUp_noRefusal srv E { ρ with wait := γw } ρ.rd gs lis
      go!"127.0.0.1:23796" cid mid R HEo $$ [Hg]
    · iframe; iframe #
    imod (etcdstart.kv_served srv E { ρ with wait := γw } ρ.rd gs lis go!"127.0.0.1:23796" cid mid R Hrb48 Hrf rfl)
      $$ [Hg Hlts Hlgs Hrds Hsts Hrslots Hbms] with ⟨Hserv, #Hkv⟩
    · unfold etcdstart.kvServeStocks
      iframe; iframe #
    imodintro
    iframe Hserv Hkv
    ipureintro; exact Hnr
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hkv, %Hnr⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    simp only [github_com.anishathalye.porcupine.Unknown]
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hserr
  wp_auto
  iunfold etcdstart.etcdKVAt at Hkv
  icases Hkv with ⟨#HPut, #HRange, #HDel, #HTxn, #HCmp⟩
  -- `NewClient(clientAddr, lg)` (etcd's default client configuration, its default retries)
  wp_apply (wp_NewClient go!"127.0.0.1:23796" lg
      (EtcdGrove.client.srvWEnv R go!"127.0.0.1:23796" [] null null [] null default)
      (by unfold plainEndpoint; decide) (by omega)) as %cl %cerr Hcl
  · iframe #
  icases Hcl with (⟨%Hcerr, #Hnc, -⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    simp only [github_com.anishathalye.porcupine.Unknown]
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hcerr
  wp_auto
  -- (D29) a write sent at most once: the member is refusal-free
  ihave #Hwo : client.clientWriteOnce (GF := GF) cl [go!"127.0.0.1:23796"] $$ []
  · iunfold client.clientWriteOnce; ipureintro
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
    subst ha; exact Hnr
  -- the instance's invariant, at the server's start store (empty)
  imod (linkvInv_alloc_boot ρ.rd.kv hlog (fun _ _ => True) [id] (LogEntry.toEntries boot 0) (srvBootLogOk_of_BootLog _ _ _ Hbf.boot) ⊤) $$ Hetcd
    with ⟨%γl, #Hlinv, Hst⟩
  -- `Check(cli, clients, ops, 0)`
  wp_apply (wp_Check γl cl go!"127.0.0.1:23796" _ E ρ.rd cid mid clients ops (W64 0) hAs
      (by omega) H0 H31 Hops Hmul) $$ [Hst] as %r %Hr
  · iframe; iframe #
  obtain ⟨-, Hok⟩ := Hr
  have Hok : r = go!"Ok" := Hok (by decide)
  subst Hok
  wp_auto
  iapply HΦ; ipureintro; left; rfl

end proof

end etcd_txnlin
end EtcdGrove
end Perennial
