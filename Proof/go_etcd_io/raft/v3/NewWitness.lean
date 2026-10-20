/-
Proof of `Spec/go_etcd_io/raft/v3/NewWitness.lean` (2026-10-20, witness support, W3b).
-/
module

public import Spec.go_etcd_io.raft.v3.NewWitness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem NewWitness.wp_proof : NewWitness.spec (GF := GF) (hG := hG) := by
  intro cfg
  wp_start
  wp_auto
  wp_alloc w as Hw
  iStructNamed Hw
  ipersist id
  ipersist storage
  ipersist preVote
  ipersist checkQuorum
  wp_auto
  iapply HΦ
  unfold ownWitness
  iexists null, interface.nil
  iframe id storage preVote checkQuorum state lastError
  isplitr
  · unfold whsOpt; ileft; ipureintro; exact ⟨rfl, rfl⟩
  ipureintro; simp

end proof

end EtcdGrove
end Perennial
