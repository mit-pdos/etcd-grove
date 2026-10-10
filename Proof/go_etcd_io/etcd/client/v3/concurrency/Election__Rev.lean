/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Election__Rev.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__Rev

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem Election.Rev.wp_proof : Election.Rev.spec (GF := GF) (hG := hG) := by
  intro e s st
  wp_start as Hst
  unfold electionState
  icases Hst with ⟨Hk, Hr, Hs, Hh, %Hsess⟩
  wp_auto
  iapply HΦ
  iframe
  ipureintro; exact Hsess

end proof

end concurrency
end EtcdGrove
end Perennial
