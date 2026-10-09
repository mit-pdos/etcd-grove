/-
Port of election_proof/proof_fmt_Sprintf.v.
-/
module

public import Spec.fmt.Sprintf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- From Perennial's `fmt.wp_Sprintf`, proved from its model of `Sprintf`
(`Perennial/TrustedCode/fmt.lean`). -/
theorem fmt.Sprintf.wp_proof : fmt.Sprintf.spec (GF := GF) (hG := hG) := by
  intro format args xs dq
  iintro %Φ ⟨#Hpkg, Hargs⟩ HΦ
  wp_apply _root_.Perennial.fmt.wp_Sprintf format args as %s _
  iapply HΦ $$ Hargs

#check @fmt.Sprintf.wp_proof

end proof

end EtcdGrove
end Perennial
