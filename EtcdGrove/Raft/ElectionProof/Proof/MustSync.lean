/-
Port of `election_proof/proof_MustSync.v` (857d09190).
-/
import EtcdGrove.Raft.ElectionProof.Spec.MustSync

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

theorem MustSync.wp_proof : MustSync.spec (GF := GF) (hG := hG) := by
  intro st prevst n
  wp_start as -
  wp_auto
  wp_if_destruct
  · wp_if_destruct
    · ispecialize HΦ $$ []
      · itrivial
      iExactEq HΦ
      congr 2 <;> simp_all
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
