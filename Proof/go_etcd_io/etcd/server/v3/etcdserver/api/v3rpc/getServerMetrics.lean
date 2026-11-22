/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/getServerMetrics.lean` (item 4, the server
start). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.getServerMetrics
public import Spec.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.NewServerMetrics
public import Spec.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.WithServerHandlingTimeHistogram
public import Spec.github_com.prometheus.client_golang.prometheus.Register
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Error
public import Perennial.Proof.sync.Link

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.getServerMetrics.wp_proof
    (hNew : grpc_prometheus.NewServerMetrics.spec (GF := GF) (hG := hG))
    (hHist : grpc_prometheus.WithServerHandlingTimeHistogram.spec (GF := GF) (hG := hG))
    (hReg : prometheus.Register.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hErr : zap.Error.spec (GF := GF) (hG := hG)) :
    v3rpc.getServerMetrics.spec (GF := GF) (hG := hG) := by
  intro mt lg
  wp_start as #Hlgn
  -- `metricsServerLock`: `v3rpc`'s package fact (item 8)
  ihave #Hvars : (v3rpc.metricsVars : IProp GF) $$ []
  · ihave Hvi : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    icases Hvi with ⟨-, -, -, -, -, #H, -⟩
    iexact H
  iunfold v3rpc.metricsVars at Hvars
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hvars] as ⟨Hlocked, HP⟩
  iunfold v3rpc.metricsP at HP
  icases HP with ⟨%m, Hm, Hmok⟩
  (try wp_auto)
  wp_if_destruct
  · icases Hmok with (⟨-, Htoks⟩ | ⟨%Hnn, -⟩)
    rotate_left
    · exact absurd rfl Hnn
    ihave #Pprom : isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus $$ []
    · iPkgInit
    (try wp_auto)
    wp_join iprop(∃ (msl : GoSlice) (os : List GoFunc), mopts_ptr ↦ msl ∗ msl ↦*□ os ∗
        □ ([∗list] o ∈ os, promSrvMetricsOpt o)) with [mopts] as ⟨%msl, %os, mopts, #Hos, #Hos'⟩
    · wp_apply hHist as %o #Ho
      (try wp_auto)
      wp_apply wp_slice_literal (V := GoFunc) (l := [o])
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      (try wp_auto)
      ihave Hn := ownSlice_nil (V := GoFunc) (GF := GF) DFrac.discard
      ihave Hc := ownSliceCap_nil (V := GoFunc) (GF := GF)
      wp_apply (wp_slice_append_persistent (V := GoFunc) slice.nil [] _ [o] (DFrac.own 1))
        $$ [Hn Hc Hosl] as %s' ⟨Hs', -, -⟩
      · iframe #; iframe
      (try wp_auto)
      isplitl []
      · ipureintro; rfl
      iexists s', [o]
      iframe
      imodintro
      iapply BigSepL.bigSepL_singleton.2; iexact Ho
    · (try wp_auto)
      iexists slice.nil, []
      iframe
      isplitl []
      · iapply (ownSlice_nil (V := GoFunc) (GF := GF) DFrac.discard)
      imodintro
      iapply BigSepL.bigSepL_nil.2; itrivial
    (try wp_auto)
    wp_apply (hNew msl os) as %m' ⟨%Hm', #Hmet, %Hdesc⟩
    · iframe #
    obtain ⟨dh, Hdh⟩ := Hdesc
    (try wp_auto)
    wp_apply (hReg _ _ Hdh (grpc_prometheus.srvDescs_ok _ dh)) $$ [Htoks] as %err %Herr
    · iframe #
      iapply grpc_prometheus.grpcKeys_srv $$ Htoks
    subst Herr
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hvars $Hlocked Hm]
    · iunfold v3rpc.metricsP
      iexists m'
      iframe
      iright
      iframe Hmet
      ipureintro; exact Hm'
    iapply HΦ
    iexact Hmet
  · (try wp_auto)
    icases Hmok with (⟨%Hn, -⟩ | ⟨%Hnn, #Hmet⟩)
    · exact absurd Hn Hif
    wp_apply sync.Mutex.wp_Unlock $$ [$Hvars $Hlocked Hm]
    · iunfold v3rpc.metricsP
      iexists m
      iframe
      iright
      iframe Hmet
      ipureintro; exact Hnn
    iapply HΦ
    iexact Hmet

end proof

end EtcdGrove
end Perennial
