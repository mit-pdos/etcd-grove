/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/linkvtxn/Main.lean` (over the examples' shared
start since 2026-10-22, D33). Lean-first (no Rocq counterpart).

The server's start is putget's `Main`'s (`Proof/.../putget/Main.lean`), at `linkvtxn`'s
configuration: `Main`'s premises in the shared start's form (`common.bootPremise_of`); the ghost
state `NewServer` takes (`common.alloc1` at the leases-off workload `putgetWorkload`);
`common.StartServer`; `common.Serve` with the ghost step `common.grpcUp_noRefusal` (the member
refusal-free, D29) then `common.kv_served` (etcd's KV calls registered at the address);
`common.NewClient` (etcd's default configuration; `clientWriteOnce`, D29). Then the instance's
invariant at the server's start store (`linkvInv_alloc_boot`: the bootstrap log changes no KV
state) and `Check(cli, clients, ops, 0)`, which returns `Ok` (`timeout = 0`), so the panic on
`Illegal` is not taken. Every step's error ends `Main` with `Unknown`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Check
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Boot
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.StartServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Served
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
namespace linkvtxn

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

set_option maxHeartbeats 800000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_StartServer : common.StartServer.spec (GF := GF) (hG := hG))
    (wp_Serve : common.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : common.NewClient.spec (GF := GF) (hG := hG))
    (wp_Check : Check.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS ESL ESE CRE CEC N id bootLog clients ops Hbf Htb Hrb48 HrbN Hck Haf Hbuq Hdbo Hms hAs
    H0 H31 Hops Hmul
  wp_start as ⟨Haddr, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hboot, #Hzap, #Hsetlg, #Htd, #Hns, #Htk, #Hstop, #Hnrl⟩
  -- `Main`'s premises in the shared start's form
  ihave #Hb := common.bootPremise_of N [id] bootLog (linkvtxnDir id) go!"linkvtxn" go!"linkvtxn"
      (common.urls1 go!"linkvtxn" go!"127.0.0.1:23806" go!"127.0.0.1:23796") id cfgOk urlsOk (putget.ccOk id)
      (fun _ h => by obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h; exact ⟨h1, by rw [h2]; rfl, h3, h4, h5, h6⟩)
      (fun _ h => by obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨h1, h2, h3, h4⟩) rfl $$ Hboot
  ihave #Hcom : common.commonPremises (GF := GF) $$ []
  · iunfold common.commonPremises; iframe #
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
  wp_apply wp_NewNop as %lg %Hlg
  (try wp_auto)
  -- the ghost state `NewServer` takes (`alloc1`)
  imod (common.alloc1 putgetWorkload id bootLog Hbf.idLow Hbf.boot (linkvtxnDir id) (dirOne_member id _) (by omega))
    with ⟨%γ, %bud, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, Hetcd⟩
  obtain ⟨hcfg, hdyn, hcc, hboot, htr, htx, hγn1, hγn2, hlog, hwl⟩ := Hal
  have hblen : bootLog.length ≤ 2 ^ 60 := by rw [Hbf.boot.1]; simp
  -- `StartServer("linkvtxn", "127.0.0.1:23806", clientAddr, lg)`
  -- (2026-10-24, rafthttp stage 6d) the one-member directory is well formed
  have Hdirok : netDirOk (linkvtxnDir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  wp_apply (wp_StartServer N go!"linkvtxn" go!"127.0.0.1:23806" go!"127.0.0.1:23796" lg bootLog
      (linkvtxnDir id) id γ bud ρ E₀ Φs γn putgetWorkload putgetWorkload_noGrant Htb Hrb48 HrbN hcfg
      hdyn hcc hboot htr htx hblen hγn1 hγn2 Hdirok Hlg Hck Haf Hbuq Hdbo) $$ [Htok Hmb]
    as %srv %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Hup⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Herr
  wp_auto
  iunfold common.memberUp at Hup
  icases Hup with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, #Hwb, #Hsf, Hwpi,
    Hbemu, Hlts, Hlgs, Hrds, Hsts, Hbms, -, HWR⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  -- `Serve(s, clientAddr)`: (D29) the member never refuses (authentication off, a voter, the
  -- members' axiom), and etcd's KV calls registered at the address
  haveI := Hms
  wp_apply (wp_Serve srv go!"127.0.0.1:23796" E { ρ with wait := γw } ρ.rd cfg
      (fun cid mid _ => iprop(common.etcdKVAt go!"127.0.0.1:23796" E { ρ with wait := γw } ρ.rd cid mid ∗
        ⌜noRefusalAt go!"127.0.0.1:23796"⌝))
      (by rw [HElg]; exact Hlg) HEtr HEw Hms Hbuq)
    $$ [Haddr Hlg3 Hbemu Hgo Hwpi HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr Hs
  · iframe; iframe #
    iintro %gs %lis %cid %mid %R Hg
    ihave ⟨Hg, %Hnr⟩ := common.grpcUp_noRefusal srv E { ρ with wait := γw } ρ.rd gs lis
      go!"127.0.0.1:23796" cid mid R HEo $$ [Hg]
    · iframe; iframe #
    imod (common.kv_served srv E { ρ with wait := γw } ρ.rd gs lis go!"127.0.0.1:23796" cid mid R Hrb48)
      $$ [Hg Hlts Hlgs Hrds Hsts Hrslots Hbms] with ⟨Hserv, #Hkv⟩
    · iframe; iframe #
    imodintro
    iframe Hserv Hkv
    ipureintro; exact Hnr
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hkv, %Hnr⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hserr
  wp_auto
  iunfold common.etcdKVAt at Hkv
  icases Hkv with ⟨#HPut, #HRange, #HDel, #HTxn⟩
  -- `NewClient(clientAddr, lg)` (etcd's default client configuration, its default retries)
  wp_apply (wp_NewClient go!"127.0.0.1:23796" lg
      (EtcdGrove.client.srvWEnv R go!"127.0.0.1:23796" [] null null [] null) Hlg
      (by unfold plainEndpoint; decide) Htb) as %cl %cerr Hcl
  icases Hcl with (⟨%Hcerr, #Hnc⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
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
  imod (linkvInv_alloc_boot ρ.rd.kv hlog (putget.ccOk id) [id] bootLog Hbf.boot (by rw [hwl]; intro; trivial) ⊤) $$ Hetcd
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

end linkvtxn
end EtcdGrove
end Perennial
