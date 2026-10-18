/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NewWatchServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.SetProgressReportInterval
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Watchable
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__MaxRequestBytesWithOverhead
public import Spec.go_uber_org.zap.NewNop
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Duration

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

theorem v3rpc.NewWatchServer.wp_proof
    (hNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hDur : zap.Duration.spec (GF := GF) (hG := hG))
    (hMRB : config.ServerConfig.MaxRequestBytesWithOverhead.spec (GF := GF) (hG := hG))
    (hWa : EtcdServer.Watchable.spec (GF := GF) (hG := hG))
    (hSet : v3rpc.SetProgressReportInterval.spec (GF := GF) (hG := hG)) :
    v3rpc.NewWatchServer.spec (GF := GF) (hG := hG) := by
  intro s E γ wsl lg0 m d
  wp_start as ⟨#Hok, #Hkv, #Hids, #Hlg, #Hm, Hd, %Hdb⟩
  iunfold v3rpc.srvIdsOk at Hids
  icases Hids with ⟨#HCl, #HMid⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pcfg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply HCl as %c ⟨%ci, %Hci, #HID⟩
  subst Hci
  (try wp_auto)
  wp_apply HID as %cid _
  (try wp_auto)
  wp_apply HMid as %mid _
  (try wp_auto)
  wp_apply (hMRB _ m)
  · iframe #
  (try wp_auto)
  wp_apply (hWa s _)
  · iframe #
  iintro -
  (try wp_auto)
  ihave %Hpn := typedPointsto_not_null _ _ _ $$ «$r0»
  iStructNamed «$r0»
  ipersist clusterID
  ipersist memberID
  ipersist maxRequestBytes
  ipersist sg
  ipersist watchable
  ipersist ag
  ihave #Hok' := Hok
  iunfold v3rpc.watchSrvOk at Hok'
  icases Hok' with ⟨-, -, -, -, #Hv, -⟩
  wp_join iprop(srv_ptr ↦ «$r0_ptr» ∗ ∃ lg : Loc, ⌜lg ≠ null⌝ ∗
      typedPointsto (structFieldRef v3rpc.watchServer go!"lg" «$r0_ptr») lg (DFrac.own 1)) with [lg srv]
    as ⟨srv, %lg, %Hlg, lgf⟩
  · wp_apply hNop as %l %Hl
    (try wp_auto)
    wp_join_done
    iframe
    ipureintro; exact Hl
  · iframe
    ipureintro; exact Hif
  ipersist lgf
  (try wp_auto)
  wp_join iprop(s_ptr ↦ s ∗ srv_ptr ↦ «$r0_ptr» ∗
      ∃ d' : w64, srvCfgFieldAddr s go!"WatchProgressNotifyInterval" ↦ d') with [Hd s srv]
    as ⟨s, srv, %d', Hd⟩
  · (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_apply (hDur _ _) as %fld _
      (try wp_auto)
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) (l := [fld])
      isplitr
      · ipureintro; rfl
      iintro %zsl ⟨-, -⟩
      (try wp_auto)
      wp_apply (hWarn lg _ _)
      · ipureintro; exact Hlg
      simp only [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.minWatchProgressInterval]
      (try wp_auto)
      wp_apply (hSet _)
      · iframe #
        ipureintro
        constructor <;> word
      (try wp_auto)
      wp_join_done
      (try iframe)
    · (try wp_auto)
      wp_apply (hSet d)
      · iframe #
        ipureintro
        rename_i h0 h1
        constructor <;> word
      (try wp_auto)
      wp_join_done
      (try iframe)
  (try wp_auto)
  iapply HΦ
  iexists «$r0_ptr», lg, cid, mid, d'
  iframe Hd
  isplitr
  · ipureintro; rfl
  iunfold v3rpc.isWatchServer
  iframe #
  ipureintro; exact ⟨Hpn, Hlg⟩

end proof

end EtcdGrove
end Perennial
