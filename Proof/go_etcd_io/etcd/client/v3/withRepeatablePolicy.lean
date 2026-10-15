/-
Proof of `Spec/go_etcd_io/etcd/client/v3/withRepeatablePolicy.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.withRepeatablePolicy

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem withRepeatablePolicy.wp_proof : withRepeatablePolicy.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold retryApplyOk
  iintro %o %p
  wp_start as Hp
  wp_auto
  simp only [go_etcd_io.etcd.client.v3.repeatable]
  wp_store
  wp_auto
  iapply HΦ
  iexists _
  iexact Hp

end proof

end EtcdGrove
end Perennial
