/-
Port of `election_proof/proof_strings_Join.v`.
-/
module

public import Spec.strings.Join
public import Perennial.Proof.strings

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

/-- Proved in Perennial (`Perennial.Proof.strings`, `wp_Join`, against the trusted model
of `Join`), which also says the result is `sep.intercalate xs`. -/
theorem strings.Join.wp_proof : strings.Join.spec (GF := GF) (hG := hG) := by
  intro elems xs dq sep
  iintro %Φ Hpre HΦ
  iapply _root_.Perennial.strings.wp_Join elems xs dq sep $$ Hpre
  inext
  iintro Helems
  iapply HΦ
  iexact Helems


end proof

end EtcdGrove
end Perennial
