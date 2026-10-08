/-
Port of election_proof/proof_pbEntryID.v.
-/
import EtcdGrove.Raft.Spec.pbEntryID

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

theorem pbEntryID.wp_proof : pbEntryID.spec (GF := GF) (hG := hG) := by
  intro p dq e
  wp_start as H
  iNamed H
  -- Lean: `wp_load` does not find the field `Access` instance of a struct points-to
  -- at a variable fraction `dq` (it does at `DFrac.own 1`), so split the struct into
  -- its fields and put it back together at the end.
  icases typedPointsto_not_null_dup _ _ _ $$ He with ⟨He, %Hnn⟩
  iStructNamed He
  wp_alloc entry_ptr as entry; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures
  wp_load; wp_pures; iclear entry
  unfold entId
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end EtcdGrove
end Perennial
