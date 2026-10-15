/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__newWatcherStreamBufLogger.lean` (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__newWatcherStreamBufLogger
public import Spec.go_etcd_io.etcd.client.v3.newBlockLogger
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Int
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Logger__Info

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem watchGRPCStream.newWatcherStreamBufLogger.wp_proof
    (wp_newBlockLogger : newBlockLogger.spec (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Int64 : zap.Int64.spec (GF := GF) (hG := hG))
    (wp_Int : zap.Int'.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Info : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.newWatcherStreamBufLogger.spec (GF := GF) (hG := hG) := by
  intro wgs ws lg key ed nowf
  wp_start as ⟨#Hlg, %Hlgn, #Hkey, #Hend, #Hnowf⟩
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  ipersist w; ipersist ws
  wp_apply wp_newBlockLogger (Qp × w64 × GoSlice) (wsLogA ws) (W64 5000000000) (W64 100000000)
    nowf _ $$ [] as %bl Hbl
  · iframe #
    imodintro
    iintro %x %n %d1 %d2 !> %Φ' HA HΦ'
    iunfold wsLogA at HA
    icases HA with ⟨Hrv, Hbuf⟩
    wp_auto
    wp_apply wp_String as %f0 -
    wp_apply wp_String as %f1 -
    wp_apply wp_Int64 as %f2 -
    wp_apply wp_Int as %f3 -
    wp_apply wp_Int as %f4 -
    wp_apply wp_Duration as %f5 -
    wp_apply wp_Duration as %f6 -
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    wp_auto
    wp_apply wp_Info $$ []
    · iframe #; ipureintro; exact Hlgn
    iapply HΦ'
    iunfold wsLogA
    iframe
  iapply HΦ; iexact Hbl

end proof

end EtcdGrove
end Perennial
