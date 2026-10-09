/-
Proof of `Spec/go_etcd_io/etcd/cache/v3/WithProgressNotifyInterval.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.WithProgressNotifyInterval

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem WithProgressNotifyInterval.wp_proof : WithProgressNotifyInterval.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start
  iapply wp_fupd
  wp_auto
  ipersist d
  imodintro
  simp only [recv_eq_func_mk]
  iapply HΦ
  unfold cfgOptSpec
  imodintro
  iintro %cp %c
  wp_start as Hc
  wp_auto
  iapply HΦ
  iexact Hc

end proof

end EtcdGrove
end Perennial
