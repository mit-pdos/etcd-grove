/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/WithContext.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.WithContext

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem WithContext.wp_proof : WithContext.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start
  iapply wp_fupd
  wp_auto
  ipersist ctx
  imodintro
  simp only [recv_eq_func_mk]
  iapply HΦ
  unfold sessionOptSpec
  imodintro
  iintro %p %o %lg
  wp_start as ⟨Hp, -⟩
  wp_auto
  iapply HΦ
  simp only [withContextM, SessionOpts.val]
  iexact Hp

end proof

end concurrency
end EtcdGrove
end Perennial
