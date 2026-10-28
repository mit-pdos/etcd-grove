/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/NewElection.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.NewElection

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem NewElection.wp_proof : NewElection.spec (GF := GF) (hG := hG) := by
  intro s γ client id pfx
  wp_start as ⟨#Hs, #Hc⟩
  iapply wp_fupd
  wp_auto
  irename «$r0» => He
  generalize «$r0_ptr» = e at *
  iStructNamed He
  ipersist session
  ipersist keyPrefix
  imodintro
  iapply HΦ
  unfold isElection electionState ElectionSt.init
  iframe
  iframe #
  ipureintro
  simp

end proof

end concurrency
end EtcdGrove
end Perennial
