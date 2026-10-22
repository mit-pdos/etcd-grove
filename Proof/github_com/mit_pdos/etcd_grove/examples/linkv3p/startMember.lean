/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/linkv3p/startMember.lean` (the partition
plan's S3a, 2026-10-20). Lean-first (no Rocq counterpart). linkv3's (`Proof/.../linkv3/
startMember.lean`, putget3's) at linkv3p's configuration: the configuration's literal, a fresh
storage registry, `NewServer`, `net.Listen` at the peer address, `s.RaftHandler()`,
`go http.Serve(l, h)`, then `net.Listen` at the client address, `s.Start()`; then the serving
steps of linkv3's `Main` (`Proof/.../linkv3/Main.lean`), for this member: `v3rpc.Server(s, nil,
nil)` (its configuration from `NewServer`'s and `Start`'s, `grpcCfgOk_of_started_w'`, with the
watchable store's reader slots), the ghost step `etcd_kv_started` (etcd's `Put`, `Range`,
`DeleteRange` and `Txn` registered at the client address) with the members' axiom `etcd_noRefusal`
before it (D29: the address refusal-free), (W2 of `notes/watch-cut-plan.md`) the `Watch` stream
served there with one run slot (`etcd_watch_served_chain`, watchkv's), `go gs.Serve(l)`. Every
step's error returns it, with the thread token.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.startMember
public import Spec.go_etcd_io.etcd.server.v3.features.NewDefaultServerFeatureGate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RaftHandler
public import Spec.net.Listen
public import Spec.net.http.Serve
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Server
public import Spec.google_golang_org.grpc.Server__Serve
public import Spec.google_golang_org.grpc.KeepaliveEnforcementPolicy
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildGap
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
/-- `EtcdGrove.client.grpcCfgOk_of_started_w` with the logger's premise inside (watchkv's; W2 of
`notes/watch-cut-plan.md`: the watchable store's reader slots kept for the watch service). -/
theorem grpcCfgOk_of_started_w' [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (tos : List GoInterface) (K : Nat) :
    ⌜cfg.Logger' ≠ null⌝ ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvServeFacts s E cfg ∗
        srvWatchReaders s E K ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.eofVar ∗ v3rpc.runsNoRequireLeader ∗
        cfg.TracerOptions' ↦*□ tos ⊢
      ∃ C : v3rpc.GrpcCfg GF, v3rpc.grpcCfgOk s C ∗
        ⌜C.A = v3rpc.srvKVAns s E ρ γr (W64 0) [] .none ∧ C.E = E⌝ ∗
        [∗list] _x ∈ List.replicate K (), mvcc.watchReader C.wsl E.s C.γ := by
  iintro ⟨%hlg, H⟩
  iapply (EtcdGrove.client.grpcCfgOk_of_started_w s E ρ γr cfg tos hlg K) $$ H

set_option maxHeartbeats 1000000 in
theorem startMember.wp_proof
    (wp_FG : features.NewDefaultServerFeatureGate.spec (GF := GF) (hG := hG))
    (wp_NewServer : ∀ [MemStorReg GF] [go_etcd_io.etcd.cache.v3.Assumptions],
      NewServer.spec (GF := GF) (hG := hG))
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_RaftHandler : EtcdServer.RaftHandler.spec (GF := GF) (hG := hG))
    (wp_Serve : net.http.Serve.spec (GF := GF) (hG := hG))
    (wp_KEP : grpc.KeepaliveEnforcementPolicy.spec (GF := GF) (hG := hG))
    (wp_Server : v3rpc.Server.spec (GF := GF) (hG := hG))
    (wp_GServe : grpc.Server.Serve.spec (GF := GF) (hG := hG)) :
    startMember.spec (GF := GF) (hG := hG) := by
  intro CS ESL ESE N name peerAddr client peer cluster lg sl₁ sl₂ sl₃ ps bootLog dir id γ bud ρ E₀
    Φs γn W hW
    Htb Hrb48 HrbN hcfg hdyn hcc hboot htr htx hblen Hγn1 Hγn2 Hdir Hlg Hck Haf Hbuq Hdbo Hms
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
      (by rw [hwl]; exact hW) Hlg (by simp) rfl (by omega) Hrb48 HrbN
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
      refine ⟨?_, ?_, hcfg, hdyn, hcc, hboot, htr, htx⟩
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
    isplitr; · ipureintro; exact Hdbo
    iapply Htk
    ipureintro; rfl
  icases Hres with (⟨%Hsn, %Herr⟩ | ⟨%Herr, %γA, %ci, %TM, %E, %γrn, %b, %HE, #Hwb, -, -, Hbuilt, Hgap,
    Hserve, Hsv, Hmon, #Hnm, HWR⟩)
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
  icases Hserve with ⟨#Hsf, Hwpi, Hbemu, Hlts, Hlgs, Hrds, Hsts, Hbms⟩
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
  obtain ⟨HEa, HEo⟩ := HE
  -- `v3rpc.Server(s, nil, nil)`: its configuration from `NewServer`'s and `Start`'s
  ihave ⟨%C, #Hgc, %HC, HWRs⟩ : ∃ C : v3rpc.GrpcCfg GF, v3rpc.grpcCfgOk srv C ∗
      ⌜C.A = v3rpc.srvKVAns srv E { ρ with wait := γw } ρ.rd (W64 0) [] .none ∧ C.E = E⌝ ∗
      [∗list] _x ∈ List.replicate 64 (), mvcc.watchReader C.wsl E.s C.γ $$ [HWR]
  · iapply (grpcCfgOk_of_started_w' srv E { ρ with wait := γw } ρ.rd _ [] 64)
    iframe; iframe #
    isplitr
    · ipureintro; exact Hlg
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
    as %gs ⟨%q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %cid, %mid, %R, %d',
      Hgsn, %Hregs, #Hq, #Hkvs, #Hws, %HR, #Hil, #Him, #Hiu, #Hims, #His, Hlg4, Hbemu2, Hgo2,
      Hwpi2⟩
  · iframe; iframe #
    isplitr
    · ipureintro; simp
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
  imod (EtcdGrove.v3rpc.etcd_watch_served_chain client pw R ims is sregs 1 Hms.watch_impl Hregs.2)
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
  iframe Hgo2 HPut HRange HDel HTxn
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
