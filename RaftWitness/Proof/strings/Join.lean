/-
Port of `election_proof/proof_strings_Join.v` (stage R4 of the raft v3.7 retarget).
-/
module

public import RaftWitness.Spec.strings.Join

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- From Perennial's `strings.wp_Join`, proved from its model of `Join`
(`Perennial/TrustedCode/strings.lean`). -/
theorem strings.Join.wp_proof : strings.Join.spec (GF := GF) (hG := hG) := by
  intro elems xs dq sep
  iintro %Φ ⟨#Hpkg, Hs⟩ HΦ
  wp_apply _root_.Perennial.strings.wp_Join elems xs dq sep $$ [$Hs] as Hs
  iapply HΦ $$ Hs


end proof

end EtcdGrove
end Perennial
