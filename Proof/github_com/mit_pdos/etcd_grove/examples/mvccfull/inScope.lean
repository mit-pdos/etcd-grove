/- Lean-first (no Rocq counterpart). The proof of `inScope`: its checks, then `runCfgOk_of`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.inScope
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.hashing
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.weightsFit
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.ScopeLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem inScope.wp_proof (wp_hashing : hashing.spec (GF := GF) (hG := hG))
    (wp_weightsFit : weightsFit.spec (GF := GF) (hG := hG)) :
    inScope.spec (GF := GF) (hG := hG) := by
  intro cfg wr dq
  wp_start as Hw
  wp_auto
  -- `cfg.Ops < 0 || cfg.Ops >= 1<<38`
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ; iframe; ipureintro; intro h; cases h
  have hops0 : 0 ≤ sint.Z cfg.Ops' := by revert Hif; word
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ; iframe; ipureintro; intro h; cases h
  have hops : sint.Z cfg.Ops' < 2 ^ 38 := by revert Hif; word
  (try wp_auto)
  -- `rd`: `max 0 cfg.Readers`
  wp_if_destruct
  · (try wp_auto)
    ihave Hrd : (∃ v : w64, rd_ptr ↦ v ∗ ⌜sint.Z v = max 0 (sint.Z cfg.Readers')⌝ : IProp GF)
      $$ [rd]
    · iexists _; iframe; ipureintro; revert Hif; word
    icases Hrd with ⟨%rdv, rd, %Hrdv⟩
    (try wp_auto)
  · (try wp_auto)
    ihave Hrd : (∃ v : w64, rd_ptr ↦ v ∗ ⌜sint.Z v = max 0 (sint.Z cfg.Readers')⌝ : IProp GF)
      $$ [rd]
    · iexists _; iframe; ipureintro; revert Hif; word
    icases Hrd with ⟨%rdv, rd, %Hrdv⟩
    (try wp_auto)
  -- `st`: `max 0 cfg.Streams`
  all_goals
    wp_if_destruct
    · (try wp_auto)
      ihave Hst : (∃ v : w64, st_ptr ↦ v ∗ ⌜sint.Z v = max 0 (sint.Z cfg.Streams')⌝ : IProp GF)
        $$ [st]
      · iexists _; iframe; ipureintro; revert Hif; word
      icases Hst with ⟨%stv, st, %Hstv⟩
      (try wp_auto)
    · (try wp_auto)
      ihave Hst : (∃ v : w64, st_ptr ↦ v ∗ ⌜sint.Z v = max 0 (sint.Z cfg.Streams')⌝ : IProp GF)
        $$ [st]
      · iexists _; iframe; ipureintro; revert Hif; word
      icases Hst with ⟨%stv, st, %Hstv⟩
      (try wp_auto)
  all_goals
    -- `rd >= 1<<28 || st >= 1<<28 || 2*rd+4*st+3 > 1<<28`
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; iframe; ipureintro; intro h; cases h
    have hrd28 : sint.Z rdv < 2 ^ 28 := by revert Hif; word
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; iframe; ipureintro; intro h; cases h
    have hst28 : sint.Z stv < 2 ^ 28 := by revert Hif; word
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; iframe; ipureintro; intro h; cases h
    have hrs : 2 * max 0 (sint.Z cfg.Readers') + 4 * max 0 (sint.Z cfg.Streams') + 3 ≤ 2 ^ 28 := by
      rw [← Hrdv, ← Hstv]; revert Hif; have := Hrdv; have := Hstv; word
    (try wp_auto)
    -- `cfg.BatchLimit > 1<<57 || cfg.CompactionBatchLimit > 1<<56`
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; iframe; ipureintro; intro h; cases h
    have hbl : sint.Z cfg.BatchLimit' ≤ 2 ^ 57 := by revert Hif; word
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; iframe; ipureintro; intro h; cases h
    have hcbl : sint.Z cfg.CompactionBatchLimit' ≤ 2 ^ 56 := by revert Hif; word
    (try wp_auto)
    -- `cfg.Depth > 37 || cfg.MaxVal > 1<<20`
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; iframe; ipureintro; intro h; cases h
    have hd : sint.Z cfg.Depth' ≤ 37 := by revert Hif; word
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; iframe; ipureintro; intro h; cases h
    have hmv : sint.Z cfg.MaxVal' ≤ 2 ^ 20 := by revert Hif; word
    (try wp_auto)
    -- `!hashing(cfg.Mix.Read) && weightsFit(cfg.Mix.Read)`
    wp_apply wp_hashing $$ [Hw] as %hh Hw
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_apply wp_weightsFit $$ [Hw] as %hf Hw
      (try wp_auto)
      iapply HΦ; iframe; ipureintro; intro hb
      exact runCfgOk_of cfg wr hops0 hops hrs hbl hcbl hd hmv
        (by revert Hif hh; cases hashingM (wr.map sint.Z) <;> simp) (hf hb)
    · (try wp_auto)
      iapply HΦ; iframe; ipureintro; intro h; cases h
end proof

end mvccfull
end EtcdGrove
end Perennial
