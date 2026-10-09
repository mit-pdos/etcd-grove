/- Port of election_proof/proof_raftLog__acceptApplying.v (857d09190).

The `||` is short-circuit: `maxAppliableIndex` runs only when the new
`applyingEntsSize` is still under the limit, which is exactly when the log can be
re-sealed for the call with `applyingEntsPaused` not yet updated (`Hpaused` holds for
either value of the flag); the size and the limit are in `LogState`, so they survive
the call. -/
module

public import Spec.go_etcd_io.raft.v3.raftLog__acceptApplying
public import Spec.go_etcd_io.raft.v3.raftLog__maxAppliableIndex

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

theorem raftLog.acceptApplying.wp_proof
    (wp_raftLog_maxAppliableIndex : raftLog.maxAppliableIndex.spec (GF := GF) (hG := hG)) :
    raftLog.acceptApplying.spec (GF := GF) (hG := hG) := by
  intro l ls i size au Hi
  wp_start as H
  iNamed H
  iNamed Hlog
  wp_auto
  rw [decide_eq_false (by rw [Hcm]; omega)]
  wp_auto
  wp_if_destruct
  · -- over the limit: paused, no `maxAppliableIndex`
    iapply HΦ
    reseal_raftLog
    all_goals (simp only [Hasz] at *; try omega)
    · intro h; cases h
  · -- under the limit: the log is re-sealed for `maxAppliableIndex`
    ihave Hlog : ownRaftLog l { ls with applying := i, apsize := ls.apsize + size }
      $$ [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
      all_goals (simp only [Hasz, Hamx] at *; try omega)
    have Hb' : ¬ uint.Z ls.apmax ≤ uint.Z (ls.apsize + size) := by rw [← Hamx, ← Hasz]; exact Hif
    wp_apply wp_raftLog_maxAppliableIndex l _ au $$ [Hlog] as %hi ⟨Hlog, -⟩
    · iexact Hlog
    iNamed Hlog
    wp_auto
    iapply HΦ
    reseal_raftLog
    all_goals (simp only [Hasz, Hamx] at *; try omega)

end proof

end EtcdGrove
end Perennial
