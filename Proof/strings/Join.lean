/-
Port of `election_proof/proof_strings_Join.v`.
-/
module

public import Spec.strings.Join

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

/-- From Perennial's `strings.wp_Join`, proved from its model of `Join`
(goose's translation of `Join`). -/
theorem strings.Join.wp_proof : strings.Join.spec (GF := GF) (hG := hG) := by
  intro elems xs dq sep Hfits
  iintro %Φ ⟨#Hpkg, Hs⟩ HΦ
  wp_apply _root_.Perennial.strings.wp_Join elems xs dq sep Hfits $$ [$Hs] as Hs
  iapply HΦ $$ Hs


end proof

end EtcdGrove
end Perennial
