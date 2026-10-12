/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Mutex__Key.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Mutex__Key

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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem Mutex.Key.wp_proof : Mutex.Key.spec (GF := GF) (hG := hG) := by
  intro m st
  wp_start as Hst
  unfold mutexState
  icases Hst with ⟨Hk, Hr, Hh⟩
  wp_auto
  iapply HΦ
  iframe

end proof

end concurrency
end EtcdGrove
end Perennial
