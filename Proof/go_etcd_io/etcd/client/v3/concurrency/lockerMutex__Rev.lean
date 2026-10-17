/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/lockerMutex__Rev.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.lockerMutex__Rev
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Mutex__Rev

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

theorem lockerMutex.Rev.wp_proof (hRev : Mutex.Rev.spec (GF := GF) (hG := hG)) :
    lockerMutex.Rev.spec (GF := GF) (hG := hG) := by
  intro lm m st
  wp_start as ⟨Hlm, Hst⟩
  wp_auto
  wp_apply hRev m st $$ [$Hpkg $Hst] as Hst
  iapply HΦ
  iframe

end proof

end concurrency
end EtcdGrove
end Perennial
