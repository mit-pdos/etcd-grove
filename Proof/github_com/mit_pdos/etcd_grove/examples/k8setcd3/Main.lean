/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8setcd3/Main.lean` (stage 6g of
`notes/k8s-etcd3-plan.md`). Lean-first (no Rocq counterpart).

As `linkvtxn/Main.lean` to the client (the server's start, verbatim at `k8setcd3`'s
configuration), then: `kubernetes.New` (one attempt per call), the seeding (`seedInv` over etcd's
start state, `seed`, cancelled at the seeded state), the store's history at the seeded state
(`histAuth_seed`), `etcd3.New` (the driver's contract), the instance's invariant at the seeded
state (`kInv_seed`) and `Check(s, st0, clients, ops, 0)`, which returns `Ok` (`timeout = 0`), so the
panic on `Illegal` is not taken. Every step's error ends `Main` with `Unknown`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Check
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.seed
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.newObj
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.New
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.New
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.NewDefaultLeaseManagerConfig
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Boot
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Contract
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
namespace k8setcd3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

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

set_option maxHeartbeats 3200000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_FG : features.NewDefaultServerFeatureGate.spec (GF := GF) (hG := hG))
    (wp_NewServer : ∀ [MemStorReg GF] [go_etcd_io.etcd.cache.v3.Assumptions],
      NewServer.spec (GF := GF) (hG := hG))
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG))
    (wp_Server : v3rpc.Server.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Serve : grpc.Server.Serve.spec (GF := GF) (hG := hG))
    (wp_kNew : kubernetes.New.spec (GF := GF) (hG := hG))
    (wp_seed : seed.spec (GF := GF) (hG := hG))
    (wp_sNew : k8s.New.spec (GF := GF) (hG := hG))
    (wp_lmc : k8s.NewDefaultLeaseManagerConfig.spec (GF := GF) (hG := hG))
    (wp_newObj : newObj.spec (GF := GF) (hG := hG))
    (hcon : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.runtime ∗
      isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ⊢
      k8s.contractOk (driverSpec (GF := GF)) codecI versionerI identityI decoderI)
    (wp_Check : Check.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS EK RT SC ST VA ESL ESE N id bootLog clients ops Hbf Htb Hrb48 HrbN Hck Haf Hbuq Hdbo Hms hAs
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
  obtain ⟨hcfg, hdyn, hcc, hboot, htr, htx, hraft, hpol, hc0, hch, hlog, hcok, hwl, hpfx, hΦs⟩ := Hal
  -- (D21 M2) the raft network, the one member's slot
  imod (netNames_alloc (srvNet γ bud) k8setcd3Dir (GMap.insert id () ∅)) with ⟨%γn, %Hγn, Hslots⟩
  ihave Hslot := (BigSepM.bigSepM_insert (GMap.lookup_empty id)).1 $$ Hslots
  icases Hslot with ⟨Hslot, -⟩
  have hblen : γ.reBoot.length ≤ 2 ^ 60 := by
    rw [hboot, Hbf.boot.1]; simp
  wp_apply (wp_NewServer _ ⟨[peerURL], [clientURL], GMap.insert go!"k8setcd3"
      (slice.mk peer (W64 (max (max (0 + 1) 0) 0)) (W64 (max (max (0 + 1) 0) 0))) ∅,
      fun _ => [peerURL]⟩ γ bud id bootLog ρ E₀ N Φs γn k8setcd3Dir hraft hpol hc0 hch hlog hcok
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
      refine ⟨?_, ?_, hcfg, hdyn, hcc, hboot, htr, htx⟩
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
    isplitr; · ipureintro; exact Hdbo
    iapply Htk
    ipureintro; rfl
  icases Hres with (⟨%Hsn, %Herr⟩ | ⟨%Herr, %γA, %ci, %TM, %E, %γn, %b, %HE, #Hwb, -, -, Hbuilt, Hgap,
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
  wp_apply (wp_Listen go!"tcp" go!"127.0.0.1:23896") $$ [Haddr] as %lis %lerr Hlis
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
      (Int.toNat sync.rwmutex.actualMaxReaders) 64 (by omega) (by omega)
      (by have := sync.actualMaxReaders_ge_2; omega) (by omega)
      $$ [Hlts Hlgs Hrds Hsts Hrslots Hbms]
  · iframe
  ihave #Hkva := client.kvServerAt_of_is p srv C.A cid mid C.n $$ Hkvs
  rw [HC.1]
  imod (client.etcd_kv_started go!"127.0.0.1:23896" gs q p srv lis E { ρ with wait := γw } ρ.rd
      cid mid C.n il im iu ims is svcs regs sregs 1 Hregs.1)
    $$ [Hgsn Hlis Hslots] with ⟨Hserv, -, #HPut, #HRange, #HDel, #HTxn⟩
  · iframe; iframe #
    iintro !>
    imodintro
    iunfold idCred
    ipureintro; exact Hrb48
  -- `go gs.Serve(l)`
  wp_apply wp_fork $$ [Hserv]
  · wp_apply (wp_Serve gs lis) $$ [$Hserv] as %serr -
    ipureintro; exact isPanic_intoVal serr
  -- `kubernetes.New(Config{Endpoints: {clientAddr}, Logger: lg, MaxUnaryRetries: 1})`
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %eps ⟨Heps, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Heps with #Heps
  ihave #Pkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes $$ []
  · iPkgInit
  wp_apply (wp_kNew _ [go!"127.0.0.1:23896"]
      ⟨R, go!"127.0.0.1:23896", [], null, null, [], null⟩) $$ [] as %kc %cerr Hcl
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
  icases Hcl with (⟨%Hcerr, %cl, #Hkc, #Hnc, Hone⟩ | %Hcfail)
  rotate_left
  · cases cerr with
    | nil => exact absurd rfl Hcfail
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hcerr
  wp_auto
  ihave #Hone := Hone $$ []
  · ipureintro; trivial
  ihave #Hone' : client.clientWriteOnce (GF := GF) cl [go!"127.0.0.1:23896"] $$ []
  · iunfold client.clientWriteOnce; ileft; iexact Hone
  -- the one member, and its KV specs
  let x : client.SrvAt GF := ⟨go!"127.0.0.1:23896", E, ρ.rd, cid, mid⟩
  ihave #Hreg1 : client.kvRegsAt x $$ []
  · iunfold client.kvRegsAt
    iframe #
  have hW : ∀ op, x.γr.kv.wl.writes op := by
    intro op; show ρ.rd.kv.wl.writes op; rw [hwl]; trivial
  -- the seeding, from the server's start state (`σb`: no key, revision `1`)
  have hboot0 : kvStateOf (kvModel ρ.rd.kv (bootEntries bootLog)) = σb := by
    have h : kvModel ρ.rd.kv (bootEntries bootLog) = [[], []] := by
      unfold kvModel
      rw [linkv.kvRaftOf_boot _ _ _ (putget.ccOk id) [id] bootLog Hbf.boot, hlog]
    rw [h]; rfl
  imod (seedInv_alloc ρ.rd.kv σb ⊤) $$ [Hetcd] with ⟨%γs, #Hsi, Hs⟩
  · rw [← hboot0]; iexact Hetcd
  ihave #Hkc' := Hkc
  iStructNamed Hkc'
  (try wp_auto)
  wp_apply (wp_seed cl x _ γs hAs hW) $$ [Hs] as %st0 %ok Hsd
  · iframe #
    iframe Hs
  icases Hsd with (%Hok | ⟨%Hok, Hs, #Hst0⟩)
  · subst Hok
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hok
  wp_auto
  imod (seedInv_cancel γs ρ.rd.kv σs2) $$ [Hs] with Hetcd
  · iframe #
    iframe Hs
  imod (histAuth_seed (GF := GF)) with ⟨%γh, Hhist⟩
  -- `etcd3.New(kc, noCompactor{}, codec{}, newObj, nil, nil, Prefix, ResourcePrefix, ...)`; the
  -- conversion to `runtime.Codec` (`type Codec Serializer`) unfolds two named types
  haveI : go.UnderlyingEq k8s_io.apimachinery.pkg.runtime.Codec.ty
      k8s_io.apimachinery.pkg.runtime.Serializer.underlying :=
    ⟨(go.UnderlyingDirectedEq.underlying_unfold (t := k8s_io.apimachinery.pkg.runtime.Codec.ty)).trans
      go.UnderlyingDirectedEq.underlying_unfold⟩
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_lmc as %lmc -
  (try wp_auto)
  let V : client.WEnv GF :=
    { R := R, addr := go!"127.0.0.1:23896", ics := [], conn := null, wc := null, pfx := [], lg := null }
  ihave #Hctx := client_ctx_field cl [go!"127.0.0.1:23896"] V $$ [Hnc]
  · iexact Hnc
  ihave #Hpr : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.runtime $$ []
  · iPkgInit
  ihave #Hpd : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 $$ []
  · iPkgInit
  ihave #Hcon := hcon $$ [Hpr Hpd]
  · isplitl; iexact Hpr; iexact Hpd
  have e1 : interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8setcd3.codec.ty #(zero_val github_com.mit_pdos.etcd_grove.examples.k8setcd3.codec) = codecI := rfl
  have e2 : interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8setcd3.identity.ty #(zero_val github_com.mit_pdos.etcd_grove.examples.k8setcd3.identity) =
      GoInterface.ok identityI := rfl
  have e3 : interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8setcd3.decoder.ty #(zero_val github_com.mit_pdos.etcd_grove.examples.k8setcd3.decoder) =
      GoInterface.ok decoderI := rfl
  have e4 : interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner.ty #(zero_val github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner) =
      GoInterface.ok versionerI := rfl
  rw [e1, e2, e3, e4]
  have hpc : path.PathCleanAbs go!"/registry" := by unfold path.PathCleanAbs; decide
  wp_apply (wp_sNew DObj driverSpec kc cl [x] V γh _ codecI _ func.nil func.nil go!"/registry"
      go!"/objs" ⟨[], go!"objs"⟩ versionerI identityI decoderI lmc hpc (by decide) (by decide))
    as %sp %err Hnew
  · simp only [List.map]
    iframe #
    isplitr
    · iapply BigSepL.bigSepL_nil.2; itrivial
    isplitr
    · ipureintro
      intro y hy
      rw [List.mem_singleton] at hy
      subst hy
      exact hW
    imodintro
    iintro %Φ' HΦ'
    wp_apply wp_newObj as %o %ho
    iapply HΦ'
    ipureintro; exact ho
  icases Hnew with ⟨%Herr, %mt, %lt, #Hstore⟩
  subst Herr
  wp_auto
  -- the driver's invariant at the seeded state, and `Check`
  let c : k8s.StoreCfg GF DObj :=
    { S := driverSpec, codec := codecI, vi := versionerI, ti := identityI, di := decoderI,
      pathPrefix := go!"/registry", resourcePrefix := go!"/objs", gr := ⟨[], go!"objs"⟩, kc := kc,
      cl := cl, ms := [x], V := V, mt := mt, lt := lt, γh := γh }
  imod (kInv_seed ρ.rd.kv c rfl rfl hW ⊤) $$ [Hetcd Hhist] with ⟨%γ, #Hinv, Hks⟩
  · iframe
  wp_apply (wp_Check γ sp c g0s st0 clients ops (W64 0) rfl rfl rfl hAs (by simp [c])
      (by omega) H0 H31 Hops Hmul (by rw [g0s_items]; simp)) $$ [Hks] as %r %hr
  · iframe #
    iframe Hks
    iapply BigSepL.bigSepL_nil.2; itrivial
  have hok : r = go!"Ok" := hr.2 (by decide)
  subst hok
  wp_auto
  iapply HΦ; ipureintro; left; rfl

end proof

end k8setcd3
end EtcdGrove
end Perennial
