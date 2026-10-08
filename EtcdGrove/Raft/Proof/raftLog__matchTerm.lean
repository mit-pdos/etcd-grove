/-
Port of election_proof/proof_raftLog__matchTerm.v.
-/
import EtcdGrove.Raft.Spec.raftLog__matchTerm
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

theorem raftLog.matchTerm.wp_proof
    (wp_raftLog_term : raftLog.term.spec (GF := GF) (hG := hG)) :
    raftLog.matchTerm.spec (GF := GF) (hG := hG) := by
  intro l ls id
  wp_start as Hpre
  iNamed Hpre
  wp_alloc l_ptr as l; wp_pures; wp_alloc id_ptr as id; wp_pures; wp_load; wp_pures; wp_load
  wp_pures; iclear l
  wp_apply wp_raftLog_term l ls $$ [$Hlog] as %t %err ⟨Hlog, %Herr, %Ht, -⟩
  wp_pures; wp_alloc err_ptr as err; wp_pures; wp_alloc t_ptr as t; wp_pures; wp_store; wp_pures
  wp_store; wp_pures; wp_load; wp_pures; iclear err
  cases err with
  | ok eok =>
    -- `err != nil`: `id.index` is out of range, so `plogTermAt` is `none`
    wp_pures; iclear id t
    iapply HΦ
    iframe
    ipureintro
    symm
    apply decide_eq_false
    intro Hm
    have Hr := plogTermAt_some_range _ _ _ _ Hm
    unfold plogLastIndexZ at Hr
    simp only [List.length_append] at Hr
    have Hc := Herr.2 (by push_cast at Hr; omega)
    cases Hc
  | nil =>
    have Ht := Ht rfl
    wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear id t
    iapply HΦ
    iframe
    ipureintro
    have : PlogMatches ls.prev (ls.sents ++ ls.uents) id ↔ t = id.term' := by
      unfold PlogMatches; rw [Ht]; simp
    simp only [this]

end proof

end EtcdGrove
end Perennial
