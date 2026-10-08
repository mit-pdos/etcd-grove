/-
Port of election_proof/proof_raftLog__findConflictByTerm.v.
-/
import EtcdGrove.Raft.Spec.raftLog__findConflictByTerm
import EtcdGrove.Raft.Spec.raftLog__term

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

theorem raftLog.findConflictByTerm.wp_proof
    (wp_raftLog_term : raftLog.term.spec (GF := GF) (hG := hG)) :
    raftLog.findConflictByTerm.spec (GF := GF) (hG := hG) := by
  intro l ls index term
  wp_start as H
  iNamed H
  wp_alloc l_ptr as l; wp_pures; wp_alloc term_ptr as term; wp_pures; wp_alloc index_ptr as index
  wp_pures
  ihave IH : iprop(∃ (idx : w64),
      "index" ∷ index_ptr ↦ idx ∗
      "Hlog" ∷ ownRaftLog l ls ∗
      "%Hidx" ∷ ⌜uint.Z idx ≤ uint.Z index⌝) $$ [index Hlog]
  · iexists index
    iframe
    ipureintro
    omega
  wp_for_core
  iNamed IH
  wp_pures; wp_load; wp_pures
  cleanup_bool_decide
  wp_if_destruct
  · wp_load; wp_pures; wp_load; wp_pures
    wp_pures; wp_alloc err_ptr as err; wp_pures; wp_alloc ourTerm_ptr as ourTerm; wp_pures; wp_store
    wp_pures; wp_store; wp_pures; wp_load; wp_pures; iclear err
    wp_apply wp_raftLog_term $$ [$Hlog] as %t %err ⟨Hlog, %Herr, %Ht, -⟩
    cases err with
    | ok eok =>
      wp_pures; wp_load; wp_pures; iclear ourTerm
      wp_for_post
      wp_pures; iclear l term index
      iapply HΦ
      iframe
      ipureintro
      exact Hidx
    | nil =>
      wp_pures; wp_load; wp_load; wp_pures
      wp_if_destruct
      · wp_load; wp_load; wp_pures; iclear ourTerm
        wp_pures; iclear l term index
        wp_for_post
        iapply HΦ
        iframe
        ipureintro
        exact Hidx
      · wp_for_post
        wp_load; wp_pures; wp_store; wp_pures; iclear ourTerm
        iframe
        iexists _
        iframe
        ipureintro
        word
  · iapply HΦ
    iframe
    ipureintro
    word

end proof

end EtcdGrove
end Perennial
