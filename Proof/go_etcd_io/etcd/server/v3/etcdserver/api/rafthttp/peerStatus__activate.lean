/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/peerStatus__activate.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peerStatus__activate
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.github_com.prometheus.client_golang.prometheus.GaugeVec__WithLabelValues
public import Perennial.Spec.time.Now

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

theorem rafthttp.peerStatus.activate.wp_proof
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hWLV : prometheus.GaugeVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG)) :
    rafthttp.peerStatus.activate.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as #Hs
  iunfold peerStatusOk at Hs
  icases Hs with ⟨%lg, %lid, %id, #Hlg, %Hlgnn, #Hlid, #Hid, #Hmu⟩
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%vAP, #HAP, %HAPl⟩, -⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock _ (peerStatusInv s) $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold peerStatusInv at Hinv
  icases Hinv with ⟨%a, %t, Ha, Ht⟩
  wp_auto
  cases a
  · wp_auto
    wp_apply hIDStringPtr _ DFrac.discard id $$ [$Hid] as %ids ⟨-, %Hids⟩
    wp_apply hZString as %f1 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply hInfo lg _ _ $$ []
    · iframe #; ipureintro; exact Hlgnn
    wp_apply wp_Now as %t' -
    (try wp_auto)
    wp_apply hIDStringPtr _ DFrac.discard lid $$ [$Hlid] as %ls ⟨-, %Hls⟩
    wp_apply hIDStringPtr _ DFrac.discard id $$ [$Hid] as %ids' ⟨-, %Hids'⟩
    wp_apply wp_slice_literal (V := GoString) [ls, ids']
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    (try wp_auto)
    wp_apply hWLV vAP _ [go!"Local", go!"Remote"] [ls, ids'] _ $$ [$Hlsl] as %g ⟨%gi, %Hgi, #Hg, -⟩
    · iframe #
      ipureintro
      refine ⟨HAPl, by simp, fun v hv => ?_⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl
      · exact utf8Valid_of_ascii _ (Hls ▸ types.idStr_ascii _)
      · exact utf8Valid_of_ascii _ (Hids' ▸ types.idStr_ascii _)
    subst Hgi
    iunfold go_etcd_io.etcd.server.v3.storage.mvcc.gaugeSpec at Hg
    icases Hg with ⟨#HInc, -, -⟩
    wp_apply HInc
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Ha Ht]
    · inext
      iunfold peerStatusInv
      iexists _, _
      iframe
    iapply HΦ
    itrivial
  · wp_auto
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
