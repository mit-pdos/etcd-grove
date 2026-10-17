/- New in etcd-io/raft#132 (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.tracker.Progress__UpdateCommit

@[expose] public section

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

/-- The builtin `min` on `uint64` (as in `Progress__MaybeDecrTo.lean`). -/
private theorem wp_min_u64 (a b : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.min [go.uint64, go.uint64])) (Val #a)) (Val #b))
    {{ RET #(w64Min a b); True }} := by
  wp_start
  wp_if_destruct
  · rw [show w64Min a b = a from ite_eq_left Hif]
    iapply HΦ; itrivial
  · rw [show w64Min a b = b from ite_eq_right Hif]
    iapply HΦ; itrivial

/-- The builtin `max` on `uint64`. -/
private theorem wp_max_u64 (a b : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.max [go.uint64, go.uint64])) (Val #a)) (Val #b))
    {{ RET #(w64Max a b); True }} := by
  wp_start
  wp_if_destruct
  · rw [show w64Max a b = a from ite_eq_left Hif]
    iapply HΦ; itrivial
  · rw [show w64Max a b = b from ite_eq_right Hif]
    iapply HΦ; itrivial

theorem tracker.Progress.UpdateCommit.wp_proof :
    tracker.Progress.UpdateCommit.spec (GF := GF) (hG := hG) := by
  intro pr p index
  wp_start as H
  iNamed H
  iNamed Hpr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := (progressAbs_Some _ _ _).1 Habs
  wp_auto
  wp_apply wp_min_u64
  wp_apply wp_max_u64
  iapply HΦ
  iapply ownProgress_intro pr _ (progressUpdateCommit p index) $$ Hpv [Hinfl]
  · dsimp only [progressUpdateCommit]
    iexact Hinfl
  ipureintro
  apply (progressAbs_Some _ _ _).2
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
  simp only [progressUpdateCommit]
  rw [h9, h3]

end proof

end EtcdGrove
end Perennial
