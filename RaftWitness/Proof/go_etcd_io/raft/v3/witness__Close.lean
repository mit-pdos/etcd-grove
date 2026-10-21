/-
Proof of `Spec/go_etcd_io/raft/v3/witness__Close.lean` (2026-10-20, witness support, W3b).
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__Close

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

theorem witness.Close.wp_proof : witness.Close.spec (GF := GF) (hG := hG) := by
  intro w id s cq pv c h N P
  wp_start as ⟨Hw, #Hs⟩
  iunfold ownWitness at Hw
  iNamed Hw
  iNamed Hs
  subst Hs
  wp_auto
  wp_bind (App (Val #(methods i.ty go!"Close" i.v)) (Val #()))
  iapply HClose $$ []
  · itrivial
  inext
  iintro -
  wp_auto
  iapply HΦ
  unfold ownWitness
  iexists p, e
  iframe Hid Hstorage HpreVote HcheckQuorum Hstate Hcache HlastError
  ipureintro; exact Hh

end proof

end EtcdGrove
end Perennial
