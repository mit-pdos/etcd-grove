/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/linkv3p/startMember.lean` (the partition
plan's S3a, 2026-10-20; over the examples' shared start since 2026-10-22, D33). Lean-first (no Rocq
counterpart). The member's start is putget3's, the shared `common.NewMember` (the configuration,
`NewServer`, its raft handler served on a listener at the peer address) at linkv3p's token, its
premises from the member's own (`common.bootPremise_of`); then `net.Listen` at the client address,
`s.Start()` (`common.wp_Start_built`); then the serving steps of linkv3's `Main`, for this member,
with the keepalive policy: `v3rpc.Server(s, nil, nil, opt)` (its configuration from the started
server's, `grpcCfgOk_of_started_w`, with the watchable store's reader slots), the ghost step
`etcd_kv_started` (etcd's `Put`, `Range`, `DeleteRange` and `Txn` registered at the client address)
with the members' axiom `etcd_noRefusal` before it (D29: the address refusal-free), (W2 of
`notes/watch-cut-plan.md`) the `Watch` stream served there with one run slot
(`etcd_watch_served_chain`, watchkv's), `go gs.Serve(l)`. Every step's error returns it, with the
thread token.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.startMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewMember
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Start
public import Spec.net.Listen
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Server
public import Spec.google_golang_org.grpc.Server__Serve
public import Spec.google_golang_org.grpc.KeepaliveEnforcementPolicy
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NoRefusal

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open putget3 (httpURL commonPremises)
open common (memberBoot memberUp)

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

set_option maxHeartbeats 1000000 in
theorem startMember.wp_proof
    (wp_NewMember : common.NewMember.spec (GF := GF) (hG := hG))
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_KEP : grpc.KeepaliveEnforcementPolicy.spec (GF := GF) (hG := hG))
    (wp_Server : v3rpc.Server.spec (GF := GF) (hG := hG))
    (wp_GServe : grpc.Server.Serve.spec (GF := GF) (hG := hG)) :
    startMember.spec (GF := GF) (hG := hG) := by
  intro CS N name peerAddr client peer cluster lg sl₁ sl₂ sl₃ ps bootLog ctxs dir id γ ρ E₀
    Φs γn
    Htb Hrb48 HrbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir Hlg Hck Haf Hbuq Hdbo Hms
  wp_start as ⟨Haddr, Hcaddr, Htok, #Hpeer, #Hcl, #Hs1, #Hs2, #Hs3, #Hboot, #Hcom, #Hcci, Hmb,
    #Hnet, Hpown⟩
  -- the premises in the shared start's form
  iunfold bootPremise at Hboot
  ihave #Hb := common.bootPremise_of N ps bootLog ctxs dir go!"linkv3p" name
      (common.urls3 name₁ name₂ name₃ initURLs3 peerAddr client) id (cfgOk name)
      (urlsOk peerAddr client) (fun _ h => h) (fun _ h => h) $$ Hboot
  ihave #Hcm' : common.commonPremises (GF := GF) $$ []
  · iunfold common.commonPremises; iunfold putget3.commonPremises at Hcom; iexact Hcom
  ihave #Hcom' := Hcom
  iunfold putget3.commonPremises at Hcom'
  icases Hcom' with ⟨-, -, -, -, -, #Hnrl⟩
  ihave #Hsls : [∗map] k ↦ sl ∈ GMap.insert name₃ sl₃ (GMap.insert name₂ sl₂
      (GMap.insert name₁ sl₁ ∅)), sl ↦*□ initURLs3 k $$ []
  · iapply (BigSepM.bigSepM_insert (by
      rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (by decide : name₂ ≠ name₃),
        GMap.lookup_insert_ne _ _ (by decide : name₁ ≠ name₃)]; rfl)).2
    isplitr; · iexact Hs3
    iapply (BigSepM.bigSepM_insert (by
      rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (by decide : name₁ ≠ name₂)]; rfl)).2
    isplitr; · iexact Hs2
    iapply (BigSepM.bigSepM_insert (GMap.lookup_empty _)).2
    isplitr; · iexact Hs1
    iapply BigSepM.bigSepM_empty.2; itrivial
  -- the imports' package facts
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  -- `io.EOF`, from its package's facts
  ihave #Heof : v3rpc.eofVar (GF := GF) $$ []
  · iapply v3rpc.eofVar_of_init
    iPkgInit
  (try wp_auto)
  -- `common.NewMember(name, peer, peerAddr, client, cluster, "linkv3p", lg)`
  wp_apply (wp_NewMember N name peerAddr client go!"linkv3p" peer cluster lg
      (GMap.insert name₃ sl₃ (GMap.insert name₂ sl₂ (GMap.insert name₁ sl₁ ∅))) initURLs3
      (common.urls3 name₁ name₂ name₃ initURLs3 peerAddr client) ps bootLog ctxs dir id γ ρ E₀ Φs γn
      (by omega) Hrb48 HrbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir
      ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩ Hlg Hck Haf Hbuq Hdbo) $$ [Haddr Hmb Hpown] as %srv %err Hres
  · iframe; iframe #
    iExactEq Hpeer; rfl
  icases Hres with (%Herr | ⟨%Herr, Hmb⟩)
  · -- `NewMember` failed: the error returned
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; iframe Htok; ipureintro; simp
  subst Herr
  wp_auto
  -- `net.Listen("tcp", client)`: the member's client address, before the server starts
  wp_apply (wp_Listen go!"tcp" client) $$ [Hcaddr] as %clis %cerr Hclis
  · iframe; ipureintro; rfl
  icases Hclis with (⟨%Hcerr, Hclis⟩ | %Hcerr)
  rotate_left
  · cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; iframe Htok; ipureintro; simp
  subst Hcerr
  wp_auto
  -- `s.Start()`
  wp_apply (common.wp_Start_built wp_Start srv ρ E₀ lg γn id N _ HrbN) $$ [Hmb Htok] as Hup
  · iframe
  (try wp_auto)
  iunfold memberUp at Hup
  icases Hup with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, #Hwb, #Hsf, Hwpi,
    Hbemu, Hlts, Hlgs, Hrds, Hsts, Hbms, Hctl, HWR⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  -- `v3rpc.Server(s, nil, nil, opt)`: its configuration from `NewServer`'s and `Start`'s
  ihave ⟨%C, #Hgc, %HC, HWRs⟩ : ∃ C : v3rpc.GrpcCfg GF, v3rpc.grpcCfgOk srv C ∗
      ⌜C.A = v3rpc.srvKVAns srv E { ρ with wait := γw } ρ.rd (W64 0) [] .none ∧ C.E = E⌝ ∗
      [∗list] _x ∈ List.replicate 64 (), mvcc.watchReader C.wsl E.s C.γ $$ [HWR]
  · iapply (EtcdGrove.client.grpcCfgOk_of_started_w srv E { ρ with wait := γw } ρ.rd cfg []
      (by rw [HElg]; exact Hlg) 64)
    iframe; iframe #
    rw [HEtr]
    iapply ownSlice_nil
  -- (2026-10-21, D28) the server option: the keepalive policy, neutral
  (try wp_auto)
  wp_apply wp_KEP as %kv %Hkv
  wp_apply wp_slice_literal (V := GoInterface) [kv]
  try (isplitr; (ipureintro; rfl))
  iintro %gslp ⟨Hgsl, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hgsl with #Hgsl
  wp_apply (wp_Server Hms srv C _ _ [kv] Hbuq) $$ [Hlg3 Hbemu Hgo Hwpi]
    as %gs ⟨%q, %p, %pw, %pa, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %cid, %mid, %R, %d',
      Hgsn, %Hregs, -, #Hq, #Hkvs, #Hws, %HR, #Hil, #Him, #Hiu, #Hims, #His, Hlg4, Hbemu2, Hgo2,
      Hwpi2⟩
  · iframe; iframe #
    isplitr
    · ipureintro; rw [HEw]; simp
    ipureintro; intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv; exact Hkv
  -- the ghost step between `Listen` and `go gs.Serve(l)`: etcd's KV specs at the address
  haveI := Hms
  icases replicate_take2 _ _ (by omega) $$ Hlts with ⟨-, -, Hlts⟩
  icases replicate_take2 _ _ (by omega) $$ Hrds with ⟨Hrd1, -, Hrds⟩
  ihave Hslots := EtcdGrove.client.etcdGrpcSlots_of_started srv E ρ.rd 1 (64 - 2) 64
      (Int.toNat sync.rwmutex.actualMaxReaders) 64 (by omega) (by omega)
      (by have := sync.actualMaxReaders_ge_2; omega) (by omega)
      $$ [Hlts Hlgs Hrds Hsts Hrslots Hbms]
  · iframe
  -- (W2) the watch server's environment is the server's; one watch run slot: two of the
  -- watchable store's readers, one of the request path's (watchkv's)
  obtain ⟨hRs, hRE, hRw, hRγ⟩ := HR
  rw [HC.2] at hRE
  ihave Hwslots := EtcdGrove.client.watchRunSlots_of R 1 64 1 (by omega) (by omega) $$ [HWRs Hrd1]
  · rw [hRw, hRγ, hRE]
    iframe HWRs
    isplitl [Hrd1]
    · simp only [List.replicate]
      iapply BigSepL.bigSepL_cons.2
      iframe Hrd1
      iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro
    rw [sync.rwmutex.actualMaxReaders_unseal]
    omega
  ihave #Hkva := EtcdGrove.client.kvServerAt_of_is p srv C.A cid mid C.n $$ Hkvs
  rw [HC.1]
  -- (D29) the member never refuses: authentication off, a voter (the members' axiom)
  ihave ⟨Hgsn, Hclis, %Hnr⟩ := (EtcdGrove.etcd_noRefusal client gs q p srv clis E
      { ρ with wait := γw } [il, im, iu] [ims, is] svcs regs sregs Hregs.1 HEo) $$
    [Hgsn Hclis]
  · iframe Hgsn Hclis; iframe #
  imod (EtcdGrove.client.etcd_kv_started client gs q p srv clis E { ρ with wait := γw } ρ.rd
      cid mid C.n il im iu ims is svcs regs sregs 1 Hregs.1)
    $$ [Hgsn Hclis Hslots] with ⟨Hserv, Hss, #HPut, #HRange, #HDel, #HTxn⟩
  · iframe Hgsn Hclis Hslots
    iframe Pv3 Psrv Hreq Hrd Hkva Hq Hil Him Hiu
    iintro !>
    imodintro
    iunfold idCred
    ipureintro; exact Hrb48
  -- (W2) the `Watch` stream served at the client address
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  imod (EtcdGrove.v3rpc.etcd_watch_served_chain client pw R ims is sregs 1 Hms.watch_impl Hregs.2.1)
    $$ [Hss Hwslots] with #Hwst
  · iframe; iframe #
  -- `go gs.Serve(l)`
  wp_apply wp_fork $$ [Hserv]
  · wp_apply (wp_GServe gs clis) $$ [$Hserv] as %serr -
    ipureintro; exact isPanic_intoVal serr
  (try wp_auto)
  iapply HΦ
  iright
  isplitr; · ipureintro; rfl
  iunfold memberServed
  iexists E, γw, cid, mid
  iframe Hgo2 HPut HRange HDel HTxn Hctl
  iframe #
  isplitl []
  · ipureintro
    exact ⟨HEa, HEo⟩
  isplitl []
  · ipureintro; exact ⟨hRs, hRE⟩
  ipureintro; exact Hnr

end proof

end linkv3p
end EtcdGrove
end Perennial
