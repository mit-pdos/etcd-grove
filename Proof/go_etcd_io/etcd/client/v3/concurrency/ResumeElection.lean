/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/ResumeElection.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.ResumeElection

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

theorem ResumeElection.wp_proof : ResumeElection.spec (GF := GF) (hG := hG) := by
  intro s γ client id pfx leaderKey leaderRev
  wp_start as ⟨#Hs, #Hc, %Hp⟩
  iapply wp_fupd
  wp_auto
  wp_alloc e as He
  iStructNamed He
  wp_auto
  ipersist session
  ipersist keyPrefix
  imodintro
  iapply HΦ
  unfold isElection electionState
  iframe
  iframe #
  ipureintro
  simp [Hp]

end proof

end concurrency
end EtcdGrove
end Perennial
