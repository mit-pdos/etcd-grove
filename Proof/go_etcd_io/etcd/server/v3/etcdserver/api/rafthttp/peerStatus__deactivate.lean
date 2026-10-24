/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/peerStatus__deactivate.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peerStatus__deactivate
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.github_com.prometheus.client_golang.prometheus.GaugeVec__WithLabelValues
public import Spec.github_com.prometheus.client_golang.prometheus.CounterVec__WithLabelValues
public import Spec.fmt.SprintfID
public import Perennial.Proof.errors.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.peerStatus.deactivate.wp_proof
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hDebug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hZError : zap.Error.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hGWLV : prometheus.GaugeVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hCWLV : prometheus.CounterVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hSprintf : fmt.SprintfID.spec (GF := GF) (hG := hG)) :
    rafthttp.peerStatus.deactivate.spec (GF := GF) (hG := hG) := by
  intro s failure reason
  wp_start as #Hs
  iunfold peerStatusOk at Hs
  icases Hs with ⟨%lg, %lid, %id, #Hlg, %Hlgnn, #Hlid, #Hid, #Hmu⟩
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%vAP, #HAP, %HAPl⟩, ⟨%vDP, #HDP, %HDPl⟩, -⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock _ (peerStatusInv s) $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold peerStatusInv at Hinv
  icases Hinv with ⟨%a, %t, Ha, Ht⟩
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go.string #failure.action', interface.mkOk go_etcd_io.etcd.client.pkg.v3.types.ID.ty #id,
      interface.mkOk go.string #failure.source', interface.mkOk go.string #reason]
  isplitr
  · ipureintro; rfl
  iintro %al ⟨Hal, -⟩
  (try wp_auto)
  wp_apply hSprintf _ _ _ (DFrac.own 1) $$ [$Hal] as %msg ⟨-, -⟩
  · ipureintro
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · left
      exact _root_.Perennial.fmt.ArgsWf.cons_string _ []
        _root_.Perennial.fmt.ArgsWf.nil _ (List.mem_singleton_self _)
    · right; rfl
    · left
      exact _root_.Perennial.fmt.ArgsWf.cons_string _ []
        _root_.Perennial.fmt.ArgsWf.nil _ (List.mem_singleton_self _)
    · left
      exact _root_.Perennial.fmt.ArgsWf.cons_string _ []
        _root_.Perennial.fmt.ArgsWf.nil _ (List.mem_singleton_self _)
  (try wp_auto)
  cases a
  · -- inactive already: log at debug level
    wp_auto
    wp_if_destruct
    · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Ha Ht]
      · inext
        iunfold peerStatusInv
        iexists _, _
        iframe
      iapply HΦ
      itrivial
    · wp_apply hIDStringPtr _ DFrac.discard id $$ [$Hid] as %ids ⟨-, -⟩
      wp_apply hZString as %f1 -
      wp_apply errors.wp_New as %e -
      wp_apply hZError as %f2 -
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply hDebug lg _ _ $$ []
      · iframe #; ipureintro; exact Hlgnn
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Ha Ht]
      · inext
        iunfold peerStatusInv
        iexists _, _
        iframe
      iapply HΦ
      itrivial
  · -- active: log, mark inactive, count
    wp_auto
    wp_apply hIDStringPtr _ DFrac.discard id $$ [$Hid] as %ids ⟨-, -⟩
    wp_apply hZString as %f1 -
    wp_apply errors.wp_New as %e -
    wp_apply hZError as %f2 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply hWarn lg _ _ $$ []
    · iframe #; ipureintro; exact Hlgnn
    (try wp_auto)
    wp_apply hIDStringPtr _ DFrac.discard lid $$ [$Hlid] as %ls ⟨-, %Hls⟩
    wp_apply hIDStringPtr _ DFrac.discard id $$ [$Hid] as %ids' ⟨-, %Hids'⟩
    wp_apply wp_slice_literal (V := GoString) [ls, ids']
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    (try wp_auto)
    wp_apply hGWLV vAP _ [go!"Local", go!"Remote"] [ls, ids'] _ $$ [$Hlsl] as %g ⟨%gi, %Hgi, #Hg, -⟩
    · iframe #
      ipureintro
      refine ⟨HAPl, by simp, fun v hv => ?_⟩
      simp only [List.mem_cons, List.mem_nil_iff, _root_.or_false] at hv
      rcases hv with rfl | rfl
      · exact utf8Valid_of_ascii _ (Hls ▸ types.idStr_ascii _)
      · exact utf8Valid_of_ascii _ (Hids' ▸ types.idStr_ascii _)
    subst Hgi
    iunfold go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec at Hg
    icases Hg with ⟨-, #HDec, -⟩
    wp_apply HDec
    (try wp_auto)
    wp_apply hIDStringPtr _ DFrac.discard lid $$ [$Hlid] as %ls2 ⟨-, %Hls2⟩
    wp_apply hIDStringPtr _ DFrac.discard id $$ [$Hid] as %ids2 ⟨-, %Hids2⟩
    wp_apply wp_slice_literal (V := GoString) [ls2, ids2]
    isplitr
    · ipureintro; rfl
    iintro %lsl2 ⟨Hlsl2, -⟩
    (try wp_auto)
    wp_apply hCWLV vDP _ [go!"Local", go!"Remote"] [ls2, ids2] _ $$ [$Hlsl2] as %c ⟨%ci, %Hci, #Hc, -⟩
    · iframe #
      ipureintro
      refine ⟨HDPl, by simp, fun v hv => ?_⟩
      simp only [List.mem_cons, List.mem_nil_iff, _root_.or_false] at hv
      rcases hv with rfl | rfl
      · exact utf8Valid_of_ascii _ (Hls2 ▸ types.idStr_ascii _)
      · exact utf8Valid_of_ascii _ (Hids2 ▸ types.idStr_ascii _)
    subst Hci
    iunfold prometheus.counterSpec at Hc
    icases Hc with ⟨#HInc, -⟩
    wp_apply HInc
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Ha Ht]
    · inext
      iunfold peerStatusInv
      iexists _, _
      iframe
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
