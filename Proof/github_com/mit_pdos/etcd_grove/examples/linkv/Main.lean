/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/linkv/Main.lean` (D20 (c), 2026-10-19).
Lean-first (no Rocq counterpart).

The server's start is putget's `Main` (`Proof/.../putget/Main.lean`, whose steps this follows
verbatim up to the client, at `linkv`'s configuration): the ghost state `NewServer` takes
(`putget.putget_alloc`), `NewServer`, `Start`, `v3rpc.Server`, `Listen`, `etcd_kv_started`
(etcd's `Put` and `Range` registered at the address), `go gs.Serve(l)`, `clientv3.New` (with
`MaxUnaryRetries: 1`, so `clientKVOnce`). Then the instance's invariant at the server's start
store (`linkvInv_alloc_boot`: the bootstrap log changes no KV state) and `Check(cli, clients, ops,
0)`, which returns `Ok` (`timeout = 0`), so the panic on `Illegal` is not taken. Every step's error
ends `Main` with `Unknown`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.Check
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Boot
public import Spec.go_uber_org.zap.NewNop
public import Spec.go_etcd_io.etcd.server.v3.features.NewDefaultServerFeatureGate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Server
public import Spec.net.Listen
public import Spec.google_golang_org.grpc.Server__Serve
public import Spec.go_etcd_io.etcd.client.v3.New
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAlloc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildGap
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.github_com.mit_pdos.etcd_grove.examples.putget.Alloc

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

omit package_sem in
/-- `client.grpcCfgOk_of_started` with the logger's premise inside (so that `iapply` finds the
configuration from `srvServeFacts`). -/
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
  iapply (client.grpcCfgOk_of_started s E ρ γr cfg tos hlg) $$ H

theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_FG : features.NewDefaultServerFeatureGate.spec (GF := GF) (hG := hG))
    (wp_NewServer : ∀ [MemStorReg GF] [go_etcd_io.etcd.cache.v3.Assumptions],
      NewServer.spec (GF := GF) (hG := hG))
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG))
    (wp_Server : v3rpc.Server.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Serve : grpc.Server.Serve.spec (GF := GF) (hG := hG))
    (wp_New : clientv3.New.spec (GF := GF) (hG := hG))
    (wp_Check : Check.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS ESL ESE N id bootLog clients ops Hbf Htb Hrb48 HrbN Hck Haf Hbuq Hnoc Hms hAs
    H0 H31 Hops Hmul
  wp_start as ⟨Haddr, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hboot, #Hzap, #Hsetlg, #Htd, #Hns, #Htk, #Hstop, #Hnrl⟩
  -- `io.EOF` and `context`'s `closedchan`, from their packages' facts
  ihave #Heof : v3rpc.eofVar (GF := GF) $$ []
  · iapply v3rpc.eofVar_of_init
    iPkgInit
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  -- the imports' package facts
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Pfeat : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.features $$ []
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
  -- `peer`, the configuration's URLs and map
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %peer ⟨Hpeer, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  wp_auto
  wp_apply wp_map_make1 (K := GoString) (V := go_etcd_io.etcd.client.pkg.v3.types.URLs)
    as %pm Hpm
  wp_apply wp_mapInsert $$ Hpm as Hpm
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %curls ⟨Hcurls, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_FG as %fgp ⟨%Hfgp, #Hfg, #Hfgc⟩
  (try wp_auto)
  -- the storage registry (D19r (B)), `bootstrap`'s to join
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := MemStorNamesRec) with ⟨%γreg, Hreg⟩
  letI : MemStorReg GF := ⟨γreg⟩
  -- the configuration's URLs, read-only from here on (D19r (F))
  imod ownSlice_persist _ _ _ $$ Hpeer with #Hpeer
  imod ownSlice_persist _ _ _ $$ Hcurls with #Hcurls
  imod ownMap_persist _ _ _ $$ Hpm with #Hpm
  -- the ghost state `NewServer` takes (`putget_alloc`)
  imod (putget.putget_alloc id bootLog Hbf (by omega)) with ⟨%γ, %bud, %ρ, %E₀, %Φs, %Hal, Hghost,
    #Hcomm, #Hcinv, #Hbinv, #Hlb, #Hidc, #HNZ0, #Hpmint, #Hrdctx, Hids, HrdCred, Hwtok, Hidx, Hcok, Hrev,
    Hnk, #Hkvinv, Hetcd⟩
  obtain ⟨hcfg, hdyn, hcc, hboot, htr, hraft, hpol, hc0, hch, hlog, hcok, hwl, hpfx, hΦs⟩ := Hal
  -- (D21 M2) the raft network, the one member's slot
  imod (netNames_alloc (srvNet γ bud) linkvDir (GMap.insert id () ∅)) with ⟨%γn, %Hγn, Hslots⟩
  ihave Hslot := (BigSepM.bigSepM_insert (GMap.lookup_empty id)).1 $$ Hslots
  icases Hslot with ⟨Hslot, -⟩
  have hblen : γ.reBoot.length ≤ 2 ^ 60 := by
    rw [hboot, Hbf.boot.1]; simp
  wp_apply (wp_NewServer _ ⟨[peerURL], [clientURL], GMap.insert go!"linkv"
      (slice.mk peer (W64 (max (max (0 + 1) 0) 0)) (W64 (max (max (0 + 1) 0) 0))) ∅,
      fun _ => [peerURL]⟩ γ bud id bootLog ρ E₀ N Φs γn linkvDir hraft hpol hc0 hch hlog hcok
      (by rw [hwl]; exact putgetWorkload_noGrant) Hlg (by simp) rfl Htb Hrb48 HrbN
      -- (D21 M3) the run bound: `SnapshotCatchUpEntries` is `2 ^ 48` (`Main`'s)
      (by
        have h48 : uint.Z (W64 281474976710656 : w64) = 2 ^ 48 := by rfl
        have hne : (W64 281474976710656 : w64) ≠ W64 0 := by decide
        simp only [hne, if_false, h48]
        omega)
      hblen
      hpfx hΦs ⟨fgp, Hfgp, rfl⟩)
    $$ [Hghost HrdCred Hids Hwtok Hidx Hcok Hrev Hnk Hreg Hslot] as %srv %err Hres
  · iframe
    iframe #
    isplitr
    · iapply Hboot
      ipureintro
      refine ⟨?_, ?_, hcfg, hdyn, hcc, hboot, htr⟩
      · unfold cfgOk; simp
      · exact ⟨rfl, rfl, ⟨_, rfl⟩, rfl⟩
    isplitr
    · iunfold bootCfgRO
      isplitr; · iExactEq Hpeer; rfl
      isplitr; · iExactEq Hcurls; rfl
      isplitr; · iExactEq Hpm; rfl
      iapply (BigSepM.bigSepM_insert (GMap.lookup_empty _)).2
      isplitr
      · iExactEq Hpeer; rfl
      iapply BigSepM.bigSepM_empty.2; itrivial
    isplitl [Hreg]
    · iunfold memStorRegAuth; iexact Hreg
    isplitr; · ipureintro; exact Hγn
    isplitr; · ipureintro; exact Hck
    isplitr; · ipureintro; exact Haf
    isplitr; · ipureintro; exact Hbuq
    isplitr; · ipureintro; exact Hnoc
    iapply Htk
    ipureintro; rfl
  icases Hres with (⟨%Hsn, %Herr⟩ | ⟨%Herr, %γA, %ci, %TM, %E, %γn, %b, %HE, #Hwb, Hbuilt, Hgap,
    Hserve, Hsv, Hmon, -⟩)
  · -- `NewServer` failed: `Main` returns
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Herr
  wp_auto
  -- `s.Start()`
  ihave Hsb := isServerBuilt_of_gap srv γA ci TM E ρ ρ.rd _ γn b (W64 0) (W64 0) (W64 0) bootKV N
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
  wp_apply (wp_Start srv γA ci TM E ρ ρ.rd _ γn b (W64 0) (W64 0) (W64 0) bootKV N HrbN rfl)
    $$ [Hsb Htok Hlg1 Hlg2 Hsv Hlgm] as ⟨%γw, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, -, -⟩
  · iframe; iframe #
  (try wp_auto)
  -- `v3rpc.Server(s, nil, nil)`: its configuration from `NewServer`'s and `Start`'s
  ihave ⟨%C, #Hgc, %HC⟩ : ∃ C : v3rpc.GrpcCfg GF, v3rpc.grpcCfgOk srv C ∗
      ⌜C.A = v3rpc.srvKVAns srv E { ρ with wait := γw } ρ.rd (W64 0) [] .none ∧ C.E = E⌝ $$ []
  · iapply (grpcCfgOk_of_started' srv E { ρ with wait := γw } ρ.rd _ [])
    iframe #
    isplitr
    · ipureintro; exact Hlg
    iapply ownSlice_nil
  wp_apply (wp_Server Hms srv C _ slice.nil [] Hbuq) $$ [Hlg3 Hbemu Hgo Hwpi]
    as %gs ⟨%q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %cid, %mid, %R, %d',
      Hgsn, %Hregs, #Hq, #Hkvs, #Hws, %HR, #Hil, #Him, #Hiu, #Hims, #His, Hlg4, Hbemu2, Hgo2,
      Hwpi2⟩
  · iframe; iframe #
    isplitr
    · ipureintro; simp
    isplitr
    · iapply ownSlice_nil
    ipureintro; intro v hv; cases hv
  -- `net.Listen("tcp", clientAddr)`
  wp_apply (wp_Listen go!"tcp" go!"127.0.0.1:23791") $$ [Haddr] as %lis %lerr Hlis
  · iframe; ipureintro; rfl
  icases Hlis with (⟨%Hlerr, Hlis⟩ | %Hlerr)
  rotate_left
  · cases lerr with
    | nil => exact absurd rfl Hlerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hlerr
  wp_auto
  -- the ghost step between `Listen` and `go gs.Serve(l)`: etcd's KV specs at the address
  haveI := Hms
  icases replicate_take2 _ _ (by omega) $$ Hlts with ⟨-, -, Hlts⟩
  icases replicate_take2 _ _ (by omega) $$ Hrds with ⟨-, -, Hrds⟩
  ihave Hslots := client.etcdGrpcSlots_of_started srv E ρ.rd 1 (64 - 2) 64
      (Int.toNat sync.rwmutex.actualMaxReaders) (by omega) (by omega)
      (by have := sync.actualMaxReaders_ge_2; omega) $$ [Hlts Hlgs Hrds Hsts Hrslots]
  · iframe
  ihave #Hkva := client.kvServerAt_of_is p srv C.A cid mid C.n $$ Hkvs
  rw [HC.1]
  imod (client.etcd_kv_started go!"127.0.0.1:23791" gs q p srv lis E { ρ with wait := γw } ρ.rd
      cid mid C.n il im iu ims is svcs regs sregs 1 Hregs.1)
    $$ [Hgsn Hlis Hslots] with ⟨Hserv, -, #HPut, #HRange, -, -⟩
  · iframe; iframe #
    iintro !>
    imodintro
    iunfold idCred
    ipureintro; exact Hrb48
  -- `go gs.Serve(l)`
  wp_apply wp_fork $$ [Hserv]
  · wp_apply (wp_Serve gs lis) $$ [$Hserv] as %serr -
    ipureintro; exact isPanic_intoVal serr
  -- `clientv3.New(Config{Endpoints: {clientAddr}, Logger: lg})`
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %eps ⟨Heps, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Heps with #Heps
  wp_apply (wp_New _ [go!"127.0.0.1:23791"]
      (EtcdGrove.client.srvWEnv R go!"127.0.0.1:23791" [] null null [] null)) $$ [] as %cl %cerr Hcl
  · iframe #
    iunfold clientCfgOk
    simp only
    iframe #
    isplitr
    · isplitr
      · iapply ownSlice_nil
      ipureintro
      refine ⟨?_, ?_⟩
      · exact plainEndpoints_singleton _ (by unfold plainEndpoint; decide)
      · simp [Hlg]
    ipureintro; exact Htb
  icases Hcl with (⟨%Hcerr, #Hnc, Hone⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hcerr
  wp_auto
  ihave #Hone := Hone $$ []
  · ipureintro; trivial
  -- the instance's invariant, at the server's start store (empty)
  imod (linkvInv_alloc_boot ρ.rd.kv hlog (putget.ccOk id) [id] bootLog Hbf.boot (by rw [hwl]; intro; trivial) ⊤) $$ Hetcd
    with ⟨%γl, #Hlinv, Hst⟩
  -- `Check(cli, clients, ops, 0)`
  wp_apply (wp_Check γl cl go!"127.0.0.1:23791" _ E ρ.rd cid mid clients ops (W64 0) hAs
      (by omega) H0 H31 Hops Hmul) $$ [Hst] as %r %Hr
  · iframe; iframe #
  obtain ⟨-, Hok⟩ := Hr
  have Hok : r = go!"Ok" := Hok (by decide)
  subst Hok
  wp_auto
  iapply HΦ; ipureintro; left; rfl

end proof

end linkv
end EtcdGrove
end Perennial
