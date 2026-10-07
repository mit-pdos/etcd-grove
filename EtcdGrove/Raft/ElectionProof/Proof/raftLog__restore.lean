/-
Port of `election_proof/proof_raftLog__restore.v`.
-/
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__restore
import EtcdGrove.Raft.ElectionProof.Spec.unstable__restore

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
  obtain ⟨prev, sents, uents, lcm, lap, snap⟩ := ls
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
  wp_apply wp_unstable_restore _ _ _ _ voters $$ [Huf Huents Huents_cap]
    as %uv' ⟨Hun, #Hsn, %Huv'⟩
  · unfold ownUnstable
    simp only [named]
    iframe Huf Huents Huents_cap Hvoters
  obtain ⟨Hoff', Hlg'⟩ := Huv'
  iNamed Hun
  ihave Hl := Hlback $$ Hu
  iapply HΦ
  dsimp only [logRestore]
  rw [← Hlg, ← Hlg']
  simp only [snapId] at Hcmlt Hlt
  iapply ownRaftLog_intro l { lv with unstable' := uv', committed' := sv.Metadata'.Index' }
      lv.storage' (some (snapId sv)) (snapId sv) [] []
      (snapId sv).index' lap sprev stored ss rfl rfl Hap ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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

end proof

end EtcdGrove
end Perennial
