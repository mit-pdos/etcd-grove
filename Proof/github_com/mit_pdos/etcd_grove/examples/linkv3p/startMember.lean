/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/linkv3p/startMember.lean` (the partition
plan's S3a, 2026-10-20). Lean-first (no Rocq counterpart). linkv3's (`Proof/.../linkv3/
startMember.lean`, putget3's) at linkv3p's configuration: the configuration's literal, a fresh
storage registry, `NewServer`, `net.Listen` at the peer address, `s.RaftHandler()`,
`go http.Serve(l, h)`, then `net.Listen` at the client address, `s.Start()`; then the serving
steps of linkv3's `Main` (`Proof/.../linkv3/Main.lean`), for this member: `v3rpc.Server(s, nil,
nil)` (its configuration from `NewServer`'s and `Start`'s, `grpcCfgOk_of_started'`), the ghost
step `etcd_kv_started` (etcd's `Put`, `Range`, `DeleteRange` and `Txn` registered at the client
address), `go
gs.Serve(l)`. Every step's error returns it, with the thread token.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.startMember
public import Spec.go_etcd_io.etcd.server.v3.features.NewDefaultServerFeatureGate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RaftHandler
public import Spec.net.Listen
public import Spec.net.http.Serve
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Server
public import Spec.google_golang_org.grpc.Server__Serve
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildGap
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open putget3 (httpURL ccOk commonPremises memberBoot memberUp)

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

omit package_sem in
/-- `EtcdGrove.client.grpcCfgOk_of_started` with the logger's premise inside (putget's; linkv3's `Main`). -/
theorem grpcCfgOk_of_started' [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (tos : List GoInterface) :
    ⌜cfg.Logger' ≠ null⌝ ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvServeFacts s E cfg ∗
        srvWatchBuilt s E ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.eofVar ∗ v3rpc.runsNoRequireLeader ∗
        cfg.TracerOptions' ↦*□ tos ⊢
      ∃ C : v3rpc.GrpcCfg GF, v3rpc.grpcCfgOk s C ∗
        ⌜C.A = v3rpc.srvKVAns s E ρ γr (W64 0) [] .none ∧ C.E = E⌝ := by
  iintro ⟨%hlg, H⟩
  iapply (EtcdGrove.client.grpcCfgOk_of_started s E ρ γr cfg tos hlg) $$ H

set_option maxHeartbeats 1000000 in
theorem startMember.wp_proof
    (wp_FG : features.NewDefaultServerFeatureGate.spec (GF := GF) (hG := hG))
    (wp_NewServer : ∀ [MemStorReg GF] [go_etcd_io.etcd.cache.v3.Assumptions],
      NewServer.spec (GF := GF) (hG := hG))
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_RaftHandler : EtcdServer.RaftHandler.spec (GF := GF) (hG := hG))
    (wp_Serve : net.http.Serve.spec (GF := GF) (hG := hG))
    (wp_Server : v3rpc.Server.spec (GF := GF) (hG := hG))
    (wp_GServe : grpc.Server.Serve.spec (GF := GF) (hG := hG)) :
    startMember.spec (GF := GF) (hG := hG) := by
  intro CS ESL ESE N name peerAddr client peer cluster lg sl₁ sl₂ sl₃ ps bootLog dir id γ bud ρ E₀
    Φs γn
    Htb Hrb48 HrbN hcfg hdyn hcc hboot htr hblen Hγn1 Hγn2 Hdir Hlg Hck Haf Hbuq Hnoc Hms
  wp_start as ⟨Haddr, Hcaddr, Htok, #Hpeer, #Hcl, #Hs1, #Hs2, #Hs3, #Hboot, #Hcom, #Hcci, Hmb,
    Hslot⟩
  iunfold bootPremise at Hboot
  iunfold commonPremises at Hcom
  icases Hcom with ⟨#Hzap, #Hsetlg, #Htd, #Hns, #Htk, #Hstop, #Hnrl⟩
  iunfold memberBoot at Hmb
  icases Hmb with ⟨%Hρ, Hghost, #Hcomm, #Hcinv, #Hbinv, #Hlb, #Hidc, #HNZ0, #Hpmint, #Hrdctx,
    Hids, HrdCred, Hwtok, Hidx, Hcok, Hrev, Hnk, #Hkvinv⟩
  obtain ⟨hraft, hpol, hc0, hch, hlog, hcok, hwl, hpfx, hΦs⟩ := Hρ
  -- the imports' package facts
  ihave #Pfeat : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features $$ []
  · iPkgInit
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
  -- the configuration's client URLs
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %curls ⟨Hcurls, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_FG as %fgp ⟨%Hfgp, #Hfg, #Hfgc⟩
  (try wp_auto)
  -- the member's storage registry (D19r (B)), its `bootstrap`'s to join
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorNamesRec) with ⟨%γreg, Hreg⟩
  letI : MemStorReg GF := ⟨γreg⟩
  imod ownSlice_persist _ _ _ $$ Hcurls with #Hcurls
  have hblen' : γ.reBoot.length ≤ 2 ^ 60 := by rw [hboot]; exact hblen
  wp_apply (wp_NewServer _ ⟨[httpURL peerAddr], [httpURL client],
      GMap.insert name₃ sl₃ (GMap.insert name₂ sl₂ (GMap.insert name₁ sl₁ ∅)), initURLs3⟩
      γ bud id bootLog ρ E₀ N Φs γn dir hraft hpol hc0 hch hlog hcok
      (by rw [hwl]; exact putgetWorkload_noGrant) Hlg (by simp) rfl Htb Hrb48 HrbN
      -- (D21 M3) the run bound: `SnapshotCatchUpEntries` is `2 ^ 48`
      (by
        have h48 : uint.Z (W64 281474976710656 : w64) = 2 ^ 48 := by rfl
        have hne : (W64 281474976710656 : w64) ≠ W64 0 := by decide
        simp only [hne, if_false, h48]
        omega)
      hblen' hpfx hΦs ⟨fgp, Hfgp, rfl⟩)
    $$ [Hghost HrdCred Hids Hwtok Hidx Hcok Hrev Hnk Hreg Hslot] as %srv %err Hres
  · iframe
    iframe #
    isplitr
    · iapply Hboot
      ipureintro
      refine ⟨?_, ?_, hcfg, hdyn, hcc, hboot, htr⟩
      · unfold cfgOk; simp
      · exact ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩
    isplitr
    · iunfold bootCfgRO
      isplitr; · iExactEq Hpeer; rfl
      isplitr; · iExactEq Hcurls; rfl
      isplitr; · iExactEq Hcl; rfl
      iapply (BigSepM.bigSepM_insert (by
        rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (by decide : name₂ ≠ name₃),
          GMap.lookup_insert_ne _ _ (by decide : name₁ ≠ name₃)]; rfl)).2
      isplitr; · iexact Hs3
      iapply (BigSepM.bigSepM_insert (by
        rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (by decide : name₁ ≠ name₂)]; rfl)).2
      isplitr; · iexact Hs2
      iapply (BigSepM.bigSepM_insert (GMap.lookup_empty _)).2
      isplitr; · iexact Hs1
      iapply BigSepM.bigSepM_empty.2; itrivial
    isplitl [Hreg]
    · iunfold memStorRegAuth; iexact Hreg
    isplitr; · ipureintro; exact ⟨Hγn1, Hγn2⟩
    isplitr; · ipureintro; exact Hck
    isplitr; · ipureintro; exact Haf
    isplitr; · ipureintro; exact Hbuq
    isplitr; · ipureintro; exact Hnoc
    iapply Htk
    ipureintro; rfl
  icases Hres with (⟨%Hsn, %Herr⟩ | ⟨%Herr, %γA, %ci, %TM, %E, %γrn, %b, %HE, #Hwb, Hbuilt, Hgap,
    Hserve, Hsv, Hmon, #Hnm, -⟩)
  · -- `NewServer` failed: the error returned
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; iframe Htok; ipureintro; simp
  subst Herr
  wp_auto
  -- `net.Listen("tcp", peerAddr)`
  wp_apply (wp_Listen go!"tcp" peerAddr) $$ [Haddr] as %lis %lerr Hlis
  · iframe; ipureintro; rfl
  icases Hlis with (⟨%Hlerr, Hlis⟩ | %Hlerr)
  rotate_left
  · cases lerr with
    | nil => exact absurd rfl Hlerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; iframe Htok; ipureintro; simp
  subst Hlerr
  wp_auto
  -- `go http.Serve(l, s.RaftHandler())`
  wp_apply (wp_RaftHandler srv γn id) as %h #Hh
  · iframe #
  (try wp_auto)
  wp_apply wp_fork $$ [Hlis]
  · wp_apply (wp_Serve lis h peerAddr γn id) $$ [Hlis] as %serr -
    · iframe Hlis Hh; ipureintro; rw [Hγn2]; exact Hdir
    ipureintro; exact isPanic_intoVal serr
  (try wp_auto)
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
  ihave Hsb := isServerBuilt_of_gap srv γA ci TM E ρ ρ.rd _ γrn b (W64 0) (W64 0) (W64 0) bootKV N
    $$ [Hbuilt Hgap]
  · iframe
  iunfold srvServeBuilt at Hserve
  icases Hserve with ⟨#Hsf, Hwpi, Hbemu, Hlts, Hlgs, Hrds, Hsts⟩
  icases replicate_take2 _ _ (by omega) $$ Hlgs with ⟨Hlg1, Hlg2, Hlgs⟩
  iunfold srvMonitorCfg at Hmon
  icases Hmon with ⟨#Hmc, #Hmd, #Hmf, Hlgm⟩
  ihave #Hoff : srvMonitorsOff srv $$ []
  · iunfold srvMonitorsOff
    isplitr; · iExactEq Hmc; rfl
    isplitr; · iExactEq Hmd; rfl
    iexists _
    iframe Hmf Hfgc
  wp_apply (wp_Start srv γA ci TM E ρ ρ.rd _ γrn b (W64 0) (W64 0) (W64 0) bootKV N HrbN rfl)
    $$ [Hsb Htok Hlg1 Hlg2 Hsv Hlgm] as ⟨%γw, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, -, -⟩
  · iframe; iframe #
  (try wp_auto)
  -- the member up (putget3's `memberUp`, as linkv3's `startMember` returns it), in the form
  -- linkv3's `Main` takes it apart to serve the member
  ihave Hup : memberUp srv ρ E₀ lg $$ [Hgo Hlg3 Hrslots Hwpi Hbemu Hlts Hlgs Hrds Hsts]
  · iunfold memberUp
    iexists E, _, γw
    iframe
    iframe #
    ipureintro
    exact ⟨HE.1, HE.2, rfl, rfl, rfl⟩
  iclear Hreq Hrd Hwb Hsf
  iunfold memberUp at Hup
  icases Hup with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, #Hwb, #Hsf, Hwpi, Hbemu,
    Hlts, Hlgs, Hrds, Hsts⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  -- `v3rpc.Server(s, nil, nil)`: its configuration from `NewServer`'s and `Start`'s
  ihave ⟨%C, #Hgc, %HC⟩ : ∃ C : v3rpc.GrpcCfg GF, v3rpc.grpcCfgOk srv C ∗
      ⌜C.A = v3rpc.srvKVAns srv E { ρ with wait := γw } ρ.rd (W64 0) [] .none ∧ C.E = E⌝ $$ []
  · iapply (grpcCfgOk_of_started' srv E { ρ with wait := γw } ρ.rd cfg [])
    iframe #
    isplitr
    · ipureintro; rw [HElg]; exact Hlg
    rw [HEtr]
    iapply ownSlice_nil
  wp_apply (wp_Server Hms srv C _ slice.nil [] Hbuq) $$ [Hlg3 Hbemu Hgo Hwpi]
    as %gs ⟨%q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %cid, %mid, %R, %d',
      Hgsn, %Hregs, #Hq, #Hkvs, #Hws, %HR, #Hil, #Him, #Hiu, #Hims, #His, Hlg4, Hbemu2, Hgo2,
      Hwpi2⟩
  · iframe; iframe #
    isplitr
    · ipureintro; rw [HEw]; simp
    isplitr
    · iapply ownSlice_nil
    ipureintro; intro v hv; cases hv
  -- the ghost step between `Listen` and `go gs.Serve(l)`: etcd's KV specs at the address
  haveI := Hms
  icases replicate_take2 _ _ (by omega) $$ Hlts with ⟨-, -, Hlts⟩
  icases replicate_take2 _ _ (by omega) $$ Hrds with ⟨-, -, Hrds⟩
  ihave Hslots := EtcdGrove.client.etcdGrpcSlots_of_started srv E ρ.rd 1 (64 - 2) 64
      (Int.toNat sync.rwmutex.actualMaxReaders) (by omega) (by omega)
      (by have := sync.actualMaxReaders_ge_2; omega) $$ [Hlts Hlgs Hrds Hsts Hrslots]
  · iframe
  ihave #Hkva := EtcdGrove.client.kvServerAt_of_is p srv C.A cid mid C.n $$ Hkvs
  rw [HC.1]
  imod (EtcdGrove.client.etcd_kv_started client gs q p srv clis E { ρ with wait := γw } ρ.rd
      cid mid C.n il im iu ims is svcs regs sregs 1 Hregs.1)
    $$ [Hgsn Hclis Hslots] with ⟨Hserv, -, #HPut, #HRange, #HDel, #HTxn⟩
  · iframe Hgsn Hclis Hslots
    iframe Pv3 Psrv Hreq Hrd Hkva Hq Hil Him Hiu
    iintro !>
    imodintro
    iunfold idCred
    ipureintro; exact Hrb48
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
  iframe Hgo2 HPut HRange HDel HTxn
  iframe #
  ipureintro
  exact ⟨HEa, HEo⟩

end proof

end linkv3p
end EtcdGrove
end Perennial
