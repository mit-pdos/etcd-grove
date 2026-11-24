/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.hasM()` (B 291-359, `OnDisk.hasM`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__hasM
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem onDisk.hasM.wp_proof : onDisk.hasM.spec (GF := GF) (hG := hG) := by
  intro g x
  wp_start as #Hx
  iunfold onDiskRO at Hx
  icases Hx with ⟨#Hs, #Hq, #Hro, #Hld, #Hll, #Hch, #Htl, #Hvi, %Hp⟩
  iunfold qitemRO at Hq
  icases Hq with ⟨#He, #Hm⟩
  ihave %Hml := msgsRO_len _ _ $$ Hm
  wp_auto
  have : decide (g.q'.M'.len = W64 0) = !x.hasM := by
    unfold OnDisk.hasM
    by_cases h0 : x.q.m = []
    · rw [h0] at Hml ⊢; simp at Hml
      have : g.q'.M'.len = W64 0 := by word
      simp [this]
    · have hne : (x.q.m != []) = true := by simpa using h0
      rw [hne]
      have hl : 0 < x.q.m.length := List.length_pos_iff.2 h0
      have : g.q'.M'.len ≠ W64 0 := by intro h; rw [h] at Hml; simp at Hml; omega
      rw [decide_eq_false this]; rfl
  rw [this, Bool.not_not]
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
