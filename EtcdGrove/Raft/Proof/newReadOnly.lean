/-
Port of election_proof/proof_newReadOnly.v.
-/
import EtcdGrove.Raft.Spec.newReadOnly

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

theorem newReadOnly.wp_proof : newReadOnly.spec (GF := GF) (hG := hG) := by
  intro o
  wp_start
  wp_alloc option_ptr as option; wp_pures; wp_load; wp_pures; iclear option
  wp_apply wp_map_make1 as %mref Hmref
  wp_pures
  wp_alloc ro' as Hro'
  wp_pures
  iapply HΦ
  unfold ownReadOnly
  iexists _, []
  iframe Hro' Hmref
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply ownSlice_nil
  isplitr
  · iapply ownSliceCap_nil
  -- no pending request: the two lists are empty
  iapply BigSepL2.bigSepL2_nil.2
  iempintro

end proof

end EtcdGrove
end Perennial
