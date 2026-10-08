/- Port of election_proof/proof_raftLog__acceptApplying.v (857d09190).

The `||` is short-circuit: `maxAppliableIndex` runs only when the new
`applyingEntsSize` is still under the limit, which is exactly when the log can be
re-sealed for the call with `applyingEntsPaused` not yet updated (`Hpaused` holds for
either value of the flag); the size and the limit are in `LogState`, so they survive
the call. -/
import EtcdGrove.Raft.Spec.raftLog__acceptApplying
import EtcdGrove.Raft.Spec.raftLog__maxAppliableIndex

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

theorem raftLog.acceptApplying.wp_proof
    (wp_raftLog_maxAppliableIndex : raftLog.maxAppliableIndex.spec (GF := GF) (hG := hG)) :
    raftLog.acceptApplying.spec (GF := GF) (hG := hG) := by
  intro l ls i size au Hi
  obtain ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ := ls
  simp only at Hi
  wp_start as H
  iNamed H
  icases (ownRaftLog_unfold l prev sents uents lcm lap snap lip lapg lpend lasz lamx).1 $$ Hlog
    with ⟨%lv, Hl, %Hcm, %Hap, %Hapg, %Hip, %Hasz, %Hamx, Hcore⟩
  unfold ownRaftLogCore
  icases Hcore with ⟨%sprev, %stored, %ss, Hcore⟩
  iNamed Hcore
  wp_alloc l_ptr as l; wp_pures; wp_alloc allowUnstable_ptr as allowUnstable; wp_pures
  wp_alloc size_ptr as size; wp_pures; wp_alloc i_ptr as i; wp_pures; wp_load; wp_pures; wp_load
  wp_load; wp_pures
  rw [decide_eq_false (by subst lcm; omega)]
  wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load
  wp_pures; wp_load; wp_load; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load; wp_load
  wp_pures; wp_load; wp_pures; iclear size
  wp_if_destruct
  · wp_load; wp_pures; wp_store; wp_pures; iclear l allowUnstable i
    -- over the limit: paused, no `maxAppliableIndex`
    iapply HΦ
    reseal_raftLog
    all_goals (dsimp only; subst_vars; try omega)
    · intro h; cases h
    · rfl
  · wp_load; wp_load; wp_pures; wp_load; wp_pures; iclear allowUnstable i
    -- under the limit: the log is re-sealed for `maxAppliableIndex`
    ihave Hlog : ownRaftLog l ⟨prev, sents, uents, lcm, lap, snap, lip, i, lpend, lasz + size, lamx⟩
      $$ [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
      all_goals (dsimp only; subst_vars; try omega)
      rfl
    have Hb' : ¬ uint.Z lamx ≤ uint.Z (lasz + size) := by subst lamx lasz; exact Hif
    wp_apply wp_raftLog_maxAppliableIndex l _ au $$ [Hlog] as %hi ⟨Hlog, -⟩
    · iexact Hlog
    icases (ownRaftLog_unfold l prev sents uents lcm lap snap lip i lpend (lasz + size) lamx).1 $$ Hlog
      with ⟨%lv, Hl, %Hcm, %Hap, %Hapg, %Hip, %Hasz, %Hamx, Hcore⟩
    unfold ownRaftLogCore
    icases Hcore with ⟨%sprev, %stored, %ss, Hcore⟩
    iNamed Hcore
    wp_pures; wp_load; wp_pures; wp_store; wp_pures; iclear l
    iapply HΦ
    reseal_raftLog
    all_goals (dsimp only; subst_vars; try omega)
    · intro _
      rw [Hasz, Hamx]
      omega

end proof

end EtcdGrove
end Perennial
