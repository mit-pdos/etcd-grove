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
  wp_start as %Hlgn
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
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hvars] as ⟨Hlocked, HP⟩
  iunfold v3rpc.metricsP at HP
  icases HP with ⟨%m, Hm, Hmok⟩
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    wp_join iprop(∃ (msl : GoSlice) (os : List GoFunc), mopts_ptr ↦ msl ∗ msl ↦*□ os ∗
        ⌜∀ o ∈ os, promSrvMetricsOpt o⌝) with [mopts] as ⟨%msl, %os, mopts, #Hos, %Hos⟩
    · wp_apply hHist as %o %Ho
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
      ipureintro
      intro o' ho'
      simp only [List.nil_append, List.mem_singleton] at ho'
      subst ho'; exact Ho
    · (try wp_auto)
      iexists slice.nil, []
      iframe
      isplitl []
      · iapply (ownSlice_nil (V := GoFunc) (GF := GF) DFrac.discard)
      ipureintro
      intro o' ho'
      simp at ho'
    (try wp_auto)
    wp_apply (hNew msl os) as %m' ⟨%Hm', #Hmet⟩
    · iframe #; ipureintro; exact Hos
    (try wp_auto)
    wp_apply (hReg m') as %err -
    · iframe #
    (try wp_auto)
    cases err with
    | ok ei =>
      (try wp_auto)
      wp_apply (hErr _) as %f -
      (try wp_auto)
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) (l := [f])
      isplitr
      · ipureintro; rfl
      iintro %zsl ⟨-, -⟩
      (try wp_auto)
      wp_apply (hWarn lg _ _)
      · iframe #; ipureintro; exact Hlgn
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock $$ [$Hvars $Hlocked Hm]
      · iunfold v3rpc.metricsP
        iexists m'
        iframe
        iright
        iexact Hmet
      iapply HΦ
      iexact Hmet
    | nil =>
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock $$ [$Hvars $Hlocked Hm]
      · iunfold v3rpc.metricsP
        iexists m'
        iframe
        iright
        iexact Hmet
      iapply HΦ
      iexact Hmet
  · (try wp_auto)
    icases Hmok with (%Hn | #Hmet)
    · exact absurd Hn Hif
    wp_apply sync.Mutex.wp_Unlock $$ [$Hvars $Hlocked Hm]
    · iunfold v3rpc.metricsP
      iexists m
      iframe
      iright
      iexact Hmet
    iapply HΦ
    iexact Hmet

end proof

end EtcdGrove
end Perennial
