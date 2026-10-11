/-
Proof of `Spec/go_etcd_io/etcd/cache/v3/demux__WaitForNextResync.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.demux__WaitForNextResync
public import Spec.go_etcd_io.etcd.cache.v3.notifier__wait

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem demux.WaitForNextResync.wp_proof (wp_wait : notifier.wait.spec (GF := GF) (hG := hG)) :
    demux.WaitForNextResync.spec (GF := GF) (hG := hG) := by
  intro d γn k0 ctx s
  wp_start as ⟨Hh, #Hlb, #Hctx⟩
  unfold demuxResyncHandle
  icases Hh with ⟨%n, #Hres, Hnh⟩
  wp_auto
  wp_apply wp_wait n γn k0 ctx s $$ [$Hpkg $Hnh $Hlb $Hctx] as %err ⟨Hnh, Hr⟩
  iapply HΦ
  iframe Hr
  iexists n
  iframe
  iframe #

end proof

end EtcdGrove
end Perennial
