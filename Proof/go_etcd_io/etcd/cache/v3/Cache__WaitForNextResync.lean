/-
Proof of `Spec/go_etcd_io/etcd/cache/v3/Cache__WaitForNextResync.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__WaitForNextResync
public import Spec.go_etcd_io.etcd.cache.v3.demux__WaitForNextResync

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Cache.WaitForNextResync.wp_proof
    (wp_WaitForNextResync : demux.WaitForNextResync.spec (GF := GF) (hG := hG)) :
    Cache.WaitForNextResync.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap γn k0 ctx s
  wp_start as ⟨#Hc, Hh, #Hlb, #Hctx⟩
  iunfold isCacheFields at Hc
  iNamed Hc
  wp_auto
  wp_apply wp_WaitForNextResync cf.demux γn k0 ctx s $$ [$Hpkg $Hh $Hlb $Hctx] as %err ⟨Hh, Hr⟩
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
