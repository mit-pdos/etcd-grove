/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Server.lean` (item 4, the server
start). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Server
public import Spec.google_golang_org.grpc.CustomCodec
public import Spec.google_golang_org.grpc.StatsHandler
public import Spec.go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc.NewServerHandler
public import Spec.google_golang_org.grpc.ChainUnaryInterceptor
public import Spec.google_golang_org.grpc.ChainStreamInterceptor
public import Spec.google_golang_org.grpc.MaxRecvMsgSize
public import Spec.google_golang_org.grpc.MaxSendMsgSize
public import Spec.google_golang_org.grpc.MaxConcurrentStreams
public import Spec.google_golang_org.grpc.NewServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.getServerMetrics
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newLogUnaryInterceptor
public import Spec.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.ServerMetrics__UnaryServerInterceptor
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newUnaryInterceptor
public import Spec.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.ServerMetrics__StreamServerInterceptor
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newStreamInterceptor
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__MaxRequestBytesWithOverhead
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewQuotaKVServer
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RegisterKVServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewWatchServer
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RegisterWatchServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewQuotaLeaseServer
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RegisterLeaseServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewClusterServer
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RegisterClusterServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewAuthServer
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RegisterAuthServer
public import Spec.google_golang_org.grpc.health.NewServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newHealthNotifier
public import Spec.google_golang_org.grpc.health.grpc_health_v1.RegisterHealthServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewMaintenanceServer
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RegisterMaintenanceServer
public import Spec.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.ServerMetrics__InitializeMetrics

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `Forall₂` of appended lists. -/
theorem v3rpc.srvOpts_forall2_app {α β : Type} {R : α → β → Prop} :
    ∀ {l1 l2 : List α} {m1 m2 : List β}, List.Forall₂ R l1 m1 → List.Forall₂ R l2 m2 →
      List.Forall₂ R (l1 ++ l2) (m1 ++ m2)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons a h1, h => .cons a (v3rpc.srvOpts_forall2_app h1 h)

/-- Neutral options, each of the kind `.neutral`. -/
theorem v3rpc.srvOpts_neutral (vs : List GoInterface) (h : ∀ v ∈ vs, grpcSrvOpt v .neutral) :
    List.Forall₂ grpcSrvOpt vs (vs.map fun _ => SrvOptKind.neutral) := by
  induction vs with
  | nil => exact .nil
  | cons v vs ih =>
    exact .cons (h v (List.mem_cons_self ..)) (ih (fun w hw => h w (List.mem_cons_of_mem _ hw)))

theorem v3rpc.srvOpts_neutral_unary (vs : List GoInterface) :
    srvOptsUnary (vs.map fun _ => SrvOptKind.neutral) = [] := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [srvOptsUnary, List.map_cons, List.flatMap_cons, SrvOptKind.unary, List.nil_append] at ih ⊢
    exact ih

theorem v3rpc.srvOpts_neutral_stream (vs : List GoInterface) :
    srvOptsStream (vs.map fun _ => SrvOptKind.neutral) = [] := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [srvOptsStream, List.map_cons, List.flatMap_cons, SrvOptKind.stream,
      List.nil_append] at ih ⊢
    exact ih

theorem v3rpc.srvOptsUnary_append (a b : List SrvOptKind) :
    srvOptsUnary (a ++ b) = srvOptsUnary a ++ srvOptsUnary b := by
  simp [srvOptsUnary, List.flatMap_append]

theorem v3rpc.srvOptsStream_append (a b : List SrvOptKind) :
    srvOptsStream (a ++ b) = srvOptsStream a ++ srvOptsStream b := by
  simp [srvOptsStream, List.flatMap_append]

theorem v3rpc.srvOptsUnary_single (k : SrvOptKind) : srvOptsUnary [k] = k.unary := by
  simp [srvOptsUnary]

theorem v3rpc.srvOptsStream_single (k : SrvOptKind) : srvOptsStream [k] = k.stream := by
  simp [srvOptsStream]

set_option maxHeartbeats 0 in
theorem v3rpc.Server.wp_proof
    (hCodec : grpc.CustomCodec.spec (GF := GF) (hG := hG))
    (hStats : grpc.StatsHandler.spec (GF := GF) (hG := hG))
    (hOtel : otelgrpc.NewServerHandler.spec (GF := GF) (hG := hG))
    (hChainU : grpc.ChainUnaryInterceptor.spec (GF := GF) (hG := hG))
    (hChainS : grpc.ChainStreamInterceptor.spec (GF := GF) (hG := hG))
    (hRecv : grpc.MaxRecvMsgSize.spec (GF := GF) (hG := hG))
    (hSend : grpc.MaxSendMsgSize.spec (GF := GF) (hG := hG))
    (hStreams : grpc.MaxConcurrentStreams.spec (GF := GF) (hG := hG))
    (hNewSrv : grpc.NewServer.spec (GF := GF) (hG := hG))
    (hMetrics : v3rpc.getServerMetrics.spec (GF := GF) (hG := hG))
    (hLogIc : v3rpc.newLogUnaryInterceptor.spec (GF := GF) (hG := hG))
    (hPromU : grpc_prometheus.ServerMetrics.UnaryServerInterceptor.spec (GF := GF) (hG := hG))
    (hUIc : v3rpc.newUnaryInterceptor.spec (GF := GF) (hG := hG))
    (hPromS : grpc_prometheus.ServerMetrics.StreamServerInterceptor.spec (GF := GF) (hG := hG))
    (hSIc : v3rpc.newStreamInterceptor.spec (GF := GF) (hG := hG))
    (hMRB : config.ServerConfig.MaxRequestBytesWithOverhead.spec (GF := GF) (hG := hG))
    (hNewKV : v3rpc.NewQuotaKVServer.spec (GF := GF) (hG := hG))
    (hRegKV : etcdserverpb.RegisterKVServer.spec (GF := GF) (hG := hG))
    (hNewW : v3rpc.NewWatchServer.spec (GF := GF) (hG := hG))
    (hRegW : etcdserverpb.RegisterWatchServer.spec (GF := GF) (hG := hG))
    (hNewL : v3rpc.NewQuotaLeaseServer.spec (GF := GF) (hG := hG))
    (hRegL : etcdserverpb.RegisterLeaseServer.spec (GF := GF) (hG := hG))
    (hNewC : v3rpc.NewClusterServer.spec (GF := GF) (hG := hG))
    (hRegC : etcdserverpb.RegisterClusterServer.spec (GF := GF) (hG := hG))
    (hNewA : v3rpc.NewAuthServer.spec (GF := GF) (hG := hG))
    (hRegA : etcdserverpb.RegisterAuthServer.spec (GF := GF) (hG := hG))
    (hHealth : health.NewServer.spec (GF := GF) (hG := hG))
    (hNotif : v3rpc.newHealthNotifier.spec (GF := GF) (hG := hG))
    (hRegH : grpc_health_v1.RegisterHealthServer.spec (GF := GF) (hG := hG))
    (hNewM : v3rpc.NewMaintenanceServer.spec (GF := GF) (hG := hG))
    (hRegM : etcdserverpb.RegisterMaintenanceServer.spec (GF := GF) (hG := hG))
    (hInit : grpc_prometheus.ServerMetrics.InitializeMetrics.spec (GF := GF) (hG := hG)) :
    v3rpc.Server.spec (GF := GF) (hG := hG) := by
  intro _
  intro s C d gsl gvs Hbuq
  wp_start as ⟨#Hc, Hlr, Hbr, Hgo, Hd, %Hdb, #Hgvs, %Hgn⟩
  iunfold v3rpc.grpcCfgOk at Hc
  icases Hc with ⟨#HKV, #Hws, #Hkv, #Hids, #Hlg0, %Hlg0n, #Hlg, %Hlgn, #Hqb, #Hmid, #Hn, #Hwd,
    #Hlead, #Hcl, #Hrc, #Hlk, #Hch, #Hstop, #Htm, #Het, #Hm, #Hfg, #Hgate, #Hmt, #Htr, #Htsl,
    #Htos, #Hmcs, #Hnrl⟩
  -- the six `ServiceDesc`s: `v3rpc`'s package fact (item 8)
  ihave #Hdescs : (v3rpc.svcDescsOk : IProp GF) $$ []
  · ihave #Pv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
    · iPkgInit
    ihave Hvi : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Pv
    icases Hvi with ⟨-, -, -, -, -, -, #H, -⟩
    iexact H
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pcfg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config $$ []
  · iPkgInit
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage $$ []
  · iPkgInit
  wp_auto
  wp_alloc cp as Hcp
  (try wp_auto)
  wp_apply (hCodec _) as %o1 %Ho1
  · ipureintro; exact v3rpc.codec_proto cp
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoInterface) (l := [o1])
  isplitr
  · ipureintro; rfl
  iintro %l1 ⟨Hl1, -⟩
  (try wp_auto)
  ihave Hn0 := ownSlice_nil (V := GoInterface) (GF := GF) DFrac.discard
  ihave Hc0 := ownSliceCap_nil (V := GoInterface) (GF := GF)
  wp_apply (wp_slice_append_persistent (V := GoInterface) slice.nil [] _ [o1] (DFrac.own 1))
    $$ [Hn0 Hc0 Hl1] as %o_1 ⟨#Ho_1, Hcap1, -⟩
  · iframe #; iframe
  (try wp_auto)
  wp_apply (hMetrics C.mt C.lg0) as %pm #Hpm
  · iframe #; ipureintro; exact Hlg0n
  (try wp_auto)
  wp_apply (hLogIc s C.lg C.wd) as %il #Hil
  · iframe #; ipureintro; exact Hlgn
  (try wp_auto)
  wp_apply (hPromU pm) as %im #Him
  · iframe #
  (try wp_auto)
  wp_apply (hUIc s C.c C.mid) as %iu #Hiu
  · iframe #
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoFunc) (l := [il, im, iu])
  isplitr
  · ipureintro; rfl
  iintro %lu ⟨Hlu, -⟩
  ipersist Hlu
  (try wp_auto)
  wp_apply (hPromS pm) as %ims #Hims
  · iframe #
  (try wp_auto)
  wp_apply (hSIc s C.c C.ch C.mid C.tm C.et) $$ [Hgo Hlr] as %is ⟨#His, Hgo, Hlr⟩
  · iframe; iframe #
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoFunc) (l := [ims, is])
  isplitr
  · ipureintro; rfl
  iintro %ls ⟨Hls, -⟩
  ipersist Hls
  (try wp_auto)
  generalize C.tr = tr
  wp_join iprop(s_ptr ↦ s ∗ ∃ (o2 : GoSlice) (vs2 : List GoInterface), opts_ptr ↦ o2 ∗
      o2 ↦*□ vs2 ∗ ownSliceCap GoInterface o2 (DFrac.own 1) ∗ ⌜∀ v ∈ vs2, grpcSrvOpt v .neutral⌝)
      with [s opts Hcap1] as ⟨s, %o2, %vs2, opts, #Ho2, Hcap2, %Hvs2⟩
  · (try wp_auto)
    iframe s
    iexists o_1, ([] ++ [o1])
    iframe; iframe #
    ipureintro
    intro v hv
    simp only [List.nil_append, List.mem_singleton] at hv
    subst hv; exact Ho1
  · (try wp_auto)
    wp_apply (hOtel C.tsl C.tos) as %h %Hh
    · iframe #
    (try wp_auto)
    wp_apply (hStats h) as %o3 %Ho3
    · ipureintro; exact Hh
    (try wp_auto)
    wp_apply wp_slice_literal (V := GoInterface) (l := [o3])
    isplitr
    · ipureintro; rfl
    iintro %l3 ⟨Hl3, -⟩
    (try wp_auto)
    wp_apply (wp_slice_append_persistent (V := GoInterface) _ _ _ [o3] (DFrac.own 1))
      $$ [Hcap1 Hl3] as %o_3 ⟨#Ho_3, Hcap3, -⟩
    · iframe; iframe #
    (try wp_auto)
    isplitl []
    · ipureintro; rfl
    iframe s
    iexists o_3, (([] ++ [o1]) ++ [o3])
    iframe; iframe #
    ipureintro
    intro v hv
    simp only [List.nil_append, List.mem_append, List.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Ho1
    · exact Ho3
  (try wp_auto)
  wp_apply (hChainU _ [il, im, iu]) as %o4 %Ho4
  · iframe #
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoInterface) (l := [o4])
  isplitr
  · ipureintro; rfl
  iintro %l4 ⟨Hl4, -⟩
  (try wp_auto)
  wp_apply (wp_slice_append_persistent (V := GoInterface) _ _ _ [o4] (DFrac.own 1))
    $$ [Hcap2 Hl4] as %o_4 ⟨#Ho_4, Hcap4, -⟩
  · iframe; iframe #
  (try wp_auto)
  wp_apply (hChainS _ [ims, is]) as %o5 %Ho5
  · iframe #
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoInterface) (l := [o5])
  isplitr
  · ipureintro; rfl
  iintro %l5 ⟨Hl5, -⟩
  (try wp_auto)
  wp_apply (wp_slice_append_persistent (V := GoInterface) _ _ _ [o5] (DFrac.own 1))
    $$ [Hcap4 Hl5] as %o_5 ⟨#Ho_5, Hcap5, -⟩
  · iframe; iframe #
  (try wp_auto)
  wp_apply (hMRB (srvCfgAddr s) C.m)
  · iframe #
  (try wp_auto)
  wp_apply (hRecv _) as %o6 %Ho6
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoInterface) (l := [o6])
  isplitr
  · ipureintro; rfl
  iintro %l6 ⟨Hl6, -⟩
  (try wp_auto)
  wp_apply (wp_slice_append_persistent (V := GoInterface) _ _ _ [o6] (DFrac.own 1))
    $$ [Hcap5 Hl6] as %o_6 ⟨#Ho_6, Hcap6, -⟩
  · iframe; iframe #
  (try wp_auto)
  (try simp only [v3rpc.maxSendBytes])
  (try wp_auto)
  wp_apply (hSend _) as %o7 %Ho7
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoInterface) (l := [o7])
  isplitr
  · ipureintro; rfl
  iintro %l7 ⟨Hl7, -⟩
  (try wp_auto)
  wp_apply (wp_slice_append_persistent (V := GoInterface) _ _ _ [o7] (DFrac.own 1))
    $$ [Hcap6 Hl7] as %o_7 ⟨#Ho_7, Hcap7, -⟩
  · iframe; iframe #
  (try wp_auto)
  wp_apply (hStreams _) as %o8 %Ho8
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoInterface) (l := [o8])
  isplitr
  · ipureintro; rfl
  iintro %l8 ⟨Hl8, -⟩
  (try wp_auto)
  wp_apply (wp_slice_append_persistent (V := GoInterface) _ _ _ [o8] (DFrac.own 1))
    $$ [Hcap7 Hl8] as %o_8 ⟨#Ho_8, Hcap8, -⟩
  · iframe; iframe #
  (try wp_auto)
  wp_apply (wp_slice_append_persistent (V := GoInterface) _ _ gsl gvs DFrac.discard)
    $$ [Hcap8] as %oF ⟨#HoF, -, -⟩
  · iframe; iframe #
  (try wp_auto)
  have Hks := v3rpc.srvOpts_forall2_app (v3rpc.srvOpts_forall2_app (v3rpc.srvOpts_forall2_app
    (v3rpc.srvOpts_forall2_app (v3rpc.srvOpts_forall2_app (v3rpc.srvOpts_forall2_app
      (v3rpc.srvOpts_neutral vs2 Hvs2) (.cons Ho4 .nil)) (.cons Ho5 .nil)) (.cons Ho6 .nil))
      (.cons Ho7 .nil)) (.cons Ho8 .nil)) (v3rpc.srvOpts_neutral gvs Hgn)
  wp_apply (hNewSrv _ _ _) as %gs Hgs
  · iframe #; ipureintro; exact Hks
  simp only [v3rpc.srvOptsUnary_append, v3rpc.srvOptsStream_append, v3rpc.srvOptsUnary_single,
    v3rpc.srvOptsStream_single, v3rpc.srvOpts_neutral_unary, v3rpc.srvOpts_neutral_stream,
    SrvOptKind.unary, SrvOptKind.stream, List.nil_append, List.append_nil]
  (try wp_auto)
  iunfold v3rpc.svcDescsOk at Hdescs
  icases Hdescs with ⟨⟨%kmds, %ksds, #HdKV, %HkvD⟩, ⟨%wsds, #HdW, %HwD⟩, HdL, HdC, HdA, HdM⟩
  iunfold v3rpc.descOk at HdL HdC HdA HdM
  icases HdL with ⟨%lmds, %lsds, #HdL, %HlD⟩
  icases HdC with ⟨%cmds, %csds, #HdC, %HcD⟩
  icases HdA with ⟨%amds, %asds, #HdA, %HaD⟩
  icases HdM with ⟨%mmds, %msds, #HdM, %HmD⟩
  ihave #HdKV := v3rpc.pbDescIs_grpc _ _ _ _ _ $$ HdKV
  ihave #HdW := v3rpc.pbDescIs_grpc _ _ _ _ _ $$ HdW
  ihave #HdL := v3rpc.pbDescIs_grpc _ _ _ _ _ $$ HdL
  ihave #HdC := v3rpc.pbDescIs_grpc _ _ _ _ _ $$ HdC
  ihave #HdA := v3rpc.pbDescIs_grpc _ _ _ _ _ $$ HdA
  ihave #HdM := v3rpc.pbDescIs_grpc _ _ _ _ _ $$ HdM
  wp_apply (hNewKV s C.A C.n C.lg C.qb C.mid Hbuq) $$ [Hlr Hbr]
    as %kv ⟨%q, %p, %cid, %mid', %Hkv, #Hq, #Hp, Hlr, Hbr⟩
  · iframe; iframe #; ipureintro; exact Hlgn
  subst Hkv
  (try wp_auto)
  wp_apply (hRegKV gs _ _ _ [] [] [] _ _ kmds ksds) $$ [Hgs] as Hgs
  · iframe; iframe #
    ipureintro
    refine ⟨List.not_mem_nil, ⟨etcdserverpb.KVServer.ty, ⟨_, _⟩, rfl, rfl, ?_⟩,
      v3rpc.kvDesc_nodup kmds ksds HkvD, ⟨_, rfl, v3rpc.ServerMethodSets.kv_te⟩⟩
    exact v3rpc.ServerMethodSets.kv_impl
  (try wp_auto)
  wp_apply (hNewW s C.E C.γ C.wsl C.lg0 C.m d) $$ [Hd]
    as %ws ⟨%pw, %lgw, %cidw, %midw, %d', %Hws', #Hpw, Hd⟩
  · iframe; iframe #; ipureintro; exact Hdb
  subst Hws'
  (try wp_auto)
  wp_apply (hRegW gs _ _ _ _ _ _ _ _ [] wsds) $$ [Hgs] as Hgs
  · iframe; iframe #
    ipureintro
    refine ⟨by decide, ⟨etcdserverpb.WatchServer.ty, ⟨_, _⟩, rfl, rfl, ?_⟩,
      v3rpc.watchDesc_nodup wsds HwD, ⟨_, rfl, v3rpc.ServerMethodSets.watch_te⟩⟩
    exact v3rpc.ServerMethodSets.watch_impl
  (try wp_auto)
  wp_apply (hNewL s C.A C.lg0 C.lg C.qb C.mid Hbuq) $$ [Hlr Hbr] as %lv ⟨%ql, %Hlv, Hlr, Hbr⟩
  · iframe; iframe #; ipureintro; exact Hlgn
  subst Hlv
  (try wp_auto)
  wp_apply (hRegL gs _ _ _ _ _ _ _ _ lmds lsds) $$ [Hgs] as Hgs
  · iframe; iframe #
    ipureintro
    refine ⟨by decide, ⟨etcdserverpb.LeaseServer.ty, ⟨_, _⟩, rfl, rfl, ?_⟩, HlD,
      ⟨_, rfl, v3rpc.ServerMethodSets.lease_te⟩⟩
    exact v3rpc.ServerMethodSets.lease_impl
  (try wp_auto)
  wp_apply (hNewC s C.c) as %pc -
  · iframe #
  (try wp_auto)
  wp_apply (hRegC gs _ _ _ _ _ _ _ _ cmds csds) $$ [Hgs] as Hgs
  · iframe; iframe #
    ipureintro
    refine ⟨by decide, ⟨etcdserverpb.ClusterServer.ty, ⟨_, _⟩, rfl, rfl, ?_⟩, HcD,
      ⟨_, rfl, v3rpc.ServerMethodSets.cluster_te⟩⟩
    exact v3rpc.ServerMethodSets.cluster_impl
  (try wp_auto)
  wp_apply (hNewA s) as %pa -
  (try wp_auto)
  wp_apply (hRegA gs _ _ _ _ _ _ _ _ amds asds) $$ [Hgs] as Hgs
  · iframe; iframe #
    ipureintro
    refine ⟨by decide, ⟨etcdserverpb.AuthServer.ty, ⟨_, _⟩, rfl, rfl, ?_⟩, HaD,
      ⟨_, rfl, v3rpc.ServerMethodSets.auth_te⟩⟩
    exact v3rpc.ServerMethodSets.auth_impl
  (try wp_auto)
  wp_apply hHealth as %hs ⟨%Hhs, #Hhsrv⟩
  (try wp_auto)
  wp_apply (hNotif hs s C.lg C.fg) $$ [Hlr] as %hn Hlr
  · iframe; iframe #; ipureintro; exact ⟨Hhs, Hlgn⟩
  (try wp_auto)
  wp_apply (hRegH gs hs) $$ [Hgs] as ⟨%rs, %srs, Hgs, %Hrs⟩
  · iframe; iframe #; ipureintro; decide
  (try wp_auto)
  wp_apply (hNewM s C.A C.lg0 C.wsl hn) as %mv %Hmv
  · iframe #
  obtain ⟨pmt, rfl⟩ := Hmv
  (try wp_auto)
  wp_apply (hRegM gs _ _ _ _ _ _ _ _ mmds msds) $$ [Hgs] as Hgs
  · iframe; iframe #
    ipureintro
    refine ⟨by decide, ⟨etcdserverpb.MaintenanceServer.ty, ⟨_, _⟩, rfl, rfl, ?_⟩, HmD,
      ⟨_, rfl, v3rpc.ServerMethodSets.maint_te⟩⟩
    exact v3rpc.ServerMethodSets.maint_impl
  (try wp_auto)
  wp_apply (hInit pm gs) $$ [Hgs] as Hgs
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  iexists q, p, pw, il, im, iu, ims, is, _, _, _, cid, mid',
    ⟨s, C.E, C.wsl, C.γ, cidw, midw, lgw, C.m + W64 (512 * 1024)⟩, d'
  iframe Hgs
  isplitr
  · ipureintro
    constructor
    · intro x hx
      have := v3rpc.kvRegs_sub q kmds HkvD.1 x hx
      simp [List.mem_append, this]
    · have := v3rpc.watchSReg_mem pw wsds HwD
      simp [List.mem_append, this]
  iframe
  iframe #
  ipureintro
  exact ⟨rfl, rfl, rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
