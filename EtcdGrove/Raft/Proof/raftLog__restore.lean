/-
Port of `election_proof/proof_raftLog__restore.v`.
-/
import EtcdGrove.Raft.Spec.raftLog__restore
import EtcdGrove.Raft.Spec.unstable__restore

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

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
private theorem isLoggerVal_open (x : GoInterface) :
    isLoggerVal (GF := GF) x ⊢ ∃ lg, ⌜x = interface.ok lg⌝ ∗ isLogger lg := by
  unfold isLoggerVal; exact .rfl

/-- Straight-line: the `Infof` through `l.logger`, the `committed` store, and
`unstable.restore` on the `unstable` field (split out with a wand taking any new
value, `raftLog_split_unstable`). The log is re-sealed at `logRestore`: the `Storage`
and its contents carried over unchanged, now shadowed (`LogStoreOk`'s `some` case). -/
theorem raftLog.restore.wp_proof
    (wp_unstable_restore : unstable.restore.spec (GF := GF) (hG := hG)) :
    raftLog.restore.spec (GF := GF) (hG := hG) := by
  intro l ls sv voters Hcmlt Hlt
  obtain ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ := ls
  wp_start as H
  iNamed H
  iNamed Hlog
  iNamed Hcore
  dsimp only at *
  icases isLoggerVal_open _ $$ Hl_logger with ⟨%lg, %Hlg, #Hlgr⟩
  wp_auto
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  try iintro %_ ⟨_, -⟩
  try wp_auto
  rw [Hlg]
  wp_apply Logger.wp_logf lg _ _ _ (by decide) $$ Hlgr
  icases raftLog_split_unstable $$ Hl with ⟨Huf, Hlback⟩
  wp_apply wp_unstable_restore _
      ⟨uents, lv.unstable'.offset', lv.unstable'.offsetInProgress', snap⟩ _ voters
      $$ [Huf Huents Huents_cap] as Hun
  · isplitl [Huf Huents Huents_cap]
    · close_unstable_log
    iframe Hvoters
  iclear Hu_logger
  icases ownUnstable_reopen _ _ _ $$ Hlback Hun
    with ⟨%uv', Hl, Hents_cap, Hents, #Hsn, #Hu_logger, %Huv'⟩
  dsimp only at Huv'
  obtain ⟨Hoff', Hoip'⟩ := Huv'
  rw [← Hoff'] at Hoip'
  iapply HΦ
  dsimp only [logRestore]
  rw [← Hlg]
  simp only [snapId] at Hcmlt Hlt
  iapply ownRaftLog_intro l { lv with unstable' := uv', committed' := sv.Metadata'.Index' }
      lv.storage' (some (snapId sv)) (snapId sv) [] []
      (snapId sv).index' lap sprev stored ss ((snapId sv).index' + W64 1) lapg lpend lasz lamx
      rfl rfl Hap ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ Hapg ?_ ?_ ?_ ?_ ?_ Hasz Hamx
    $$ Hl HisStorage HStorage Hsn Hents Hents_cap Hl_logger Hu_logger
  all_goals simp only [snapId, List.append_nil, List.length_nil, Int.natCast_zero, Int.add_zero]
  · intro k e h; simp at h
  · word
  · exact ⟨rfl, rfl, by word, by word⟩
  · rw [Hoff']; word
  · intro e h; simp at h
  · constructor
    · omega
    · rw [Hcm] at Happlied; rw [Hap] at Happlied; word
  · intro h; cases h
  · omega
  · intro h; cases h
  · rw [Hoip', Hoff']
  · rw [Hoip']; omega
  · intro h; cases h
  · rw [Hcm] at Happlying; omega
  · exact Hpaused

end proof

end EtcdGrove
end Perennial
