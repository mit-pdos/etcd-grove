/-
Port of election_proof/proof_fmt_Sprintf.v.
-/
module

public import Spec.fmt.Sprintf
public import Perennial.Proof.fmt

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

/-- Proved in Perennial (`Perennial.Proof.fmt`, `wp_Sprintf`, against the trusted model of
`Sprintf`); the slice points-to is framed. -/
theorem fmt.Sprintf.wp_proof : fmt.Sprintf.spec (GF := GF) (hG := hG) := by
  intro format args xs dq
  iintro %Φ ⟨#Hinit, Hargs⟩ HΦ
  iapply _root_.Perennial.fmt.wp_Sprintf format args $$ [Hinit]
  · iexact Hinit
  iintro %s
  inext
  iintro -
  iapply HΦ
  iexact Hargs

end proof

end EtcdGrove
end Perennial
