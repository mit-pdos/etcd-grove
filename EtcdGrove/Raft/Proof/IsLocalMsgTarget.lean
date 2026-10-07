/-
Port of `election_proof/proof_IsLocalMsgTarget.v`.
-/
import EtcdGrove.Raft.Spec.IsLocalMsgTarget

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

theorem IsLocalMsgTarget.wp_proof : IsLocalMsgTarget.spec (GF := GF) (hG := hG) := by
  intro id
  wp_start as -
  wp_auto
  wp_if_destruct
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
