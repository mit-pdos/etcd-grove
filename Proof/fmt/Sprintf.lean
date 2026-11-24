/-
Port of election_proof/proof_fmt_Sprintf.v.
-/
module

public import Spec.fmt.Sprintf
public import Perennial.Proof.fmt.Link

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

/-- From Perennial's spec of the real `Sprintf` (`fmt.wp_Sprintf`, translated and proved, real
`fmt` stage 1), through `fmt.wp_Sprintf_pure`. -/
theorem fmt.Sprintf.wp_proof : fmt.Sprintf.spec (GF := GF) (hG := hG) :=
  fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf

end proof

end EtcdGrove
end Perennial
