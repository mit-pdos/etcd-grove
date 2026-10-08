/-
Port of `election_proof/proof_isHardStateEqual.v`.
-/
import EtcdGrove.Raft.Spec.isHardStateEqual

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

theorem isHardStateEqual.wp_proof : isHardStateEqual.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start as -
  wp_alloc b_ptr as b; wp_pures; wp_alloc a_ptr as a; wp_pures; wp_load; wp_pures; wp_load; wp_pures
  wp_if_destruct
  -- TODO(no-wp-auto): wp_if_destruct runs: wp_load; wp_pures; wp_load; wp_pures; iclear b a | ∅
  · wp_load; wp_pures; wp_load; wp_pures
    wp_if_destruct <;>
    · ispecialize HΦ $$ []
      · itrivial
      iExactEq HΦ
      congr 2 <;> simp_all
  · ispecialize HΦ $$ []
    · itrivial
    iExactEq HΦ
    congr 2 <;> simp_all

end proof

end EtcdGrove
end Perennial
