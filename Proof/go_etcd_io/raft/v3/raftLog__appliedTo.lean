/-
Port of election_proof/proof_raftLog__appliedTo.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raftLog__appliedTo

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
theorem raftLog.appliedTo.wp_proof : raftLog.appliedTo.spec (GF := GF) (hG := hG) := by
  intro l ls i size Hi
  wp_start as Hlog
  iNamed Hlog
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
    reseal_raftLog
  all_goals
    simp only [Hcm, Hap, Hapg, Hasz, Hamx] at *
    first
      | rfl
      | omega
      | (intro Hn; have := Hpapplied Hn; omega)
      | (unfold w64Max; split <;> first | rfl | omega)
      | (split <;> first | rfl | omega)
      | (intro Hpz; simp only [decide_eq_false_iff_not] at Hpz; split <;> word)

end proof

end EtcdGrove
end Perennial
