/-
Port of election_proof/proof_raftLog__appliedTo.v.
-/
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__appliedTo

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
theorem raftLog.appliedTo.wp_proof : raftLog.appliedTo.spec (GF := GF) (hG := hG) := by
  intro l ls i size Hi
  obtain ⟨prev, sents, uents, lcm, lap, snap⟩ := ls
  simp only at Hi ⊢
  wp_start as Hlog
  icases (ownRaftLog_unfold l prev sents uents lcm lap snap).1 $$ Hlog with ⟨%lv, Hl, %Hcm, %Hap, Hcore⟩
  wp_auto
  rw [decide_eq_false (by rw [Hcm]; omega)]
  wp_auto
  rw [decide_eq_false (by rw [Hap]; omega)]
  wp_auto
  -- `max(l.applying, i)`
  wp_func_call
  wp_call
  wp_if_destruct <;> wp_if_destruct
  all_goals
    iapply HΦ
    iunfold ownRaftLogCore at Hcore
    icases Hcore with ⟨%sprev, %stored, %ss, Hcore⟩
    iNamed Hcore
    reseal_raftLog
  all_goals
    simp only
    subst Hcm Hap
    first
      | omega
      | (intro Hn; have := Hpapplied Hn; omega)

end proof

end EtcdGrove
end Perennial
