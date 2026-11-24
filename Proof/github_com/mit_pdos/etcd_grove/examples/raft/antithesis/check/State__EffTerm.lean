/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `State.EffTerm` (B 152).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__EffTerm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Min
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

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

theorem State.EffTerm.wp_proof (wp_Min : Min.spec (GF := GF) (hG := hG)) :
    State.EffTerm.spec (GF := GF) (hG := hG) := by
  intro p s n
  wp_start as ⟨#Hs, %Hn⟩
  obtain ⟨Hn0, Hlt⟩ := Hn
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  icases undoRO_at g.Undo' s.undo n ⟨Hn0, by rw [HWf.len_undo]; exact Hlt⟩ $$ HUndo with ⟨%u, #Hua, #Hu⟩
  icases intsRO_at g.CurrentTerm' s.currentTerm n ⟨Hn0, by rw [HWf.len_currentTerm]; exact Hlt⟩ $$ HCurrentTerm with ⟨%ct, #Hct, %Hct⟩
  wp_auto
  wp_apply wp_load_at _ _ u Hn0 $$ [Hua]
  · iexact Hua
  unfold State.effTerm
  cases hu : s.undo[sint.nat n]! with
  | none =>
    iunfold preRO at Hu
    icases Hu with %Hnull
    subst Hnull
    wp_auto
    wp_apply wp_load_at _ _ ct Hn0 $$ [Hct]
    · iexact Hct
    try wp_auto
    iapply HΦ; ipureintro; exact Hct
  | some pu =>
    iunfold preRO at Hu
    icases Hu with ⟨%gp, #Hgp, %Hpf, #-, #-, #-, #-⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgp
    wp_if_destruct
    · exact absurd rfl Hnn
    wp_apply wp_load_at _ _ ct Hn0 $$ [Hct]
    · iexact Hct
    try wp_auto
    wp_apply wp_load_at _ _ u Hn0 $$ [Hua]
    · iexact Hua
    ihave #Hgp' := Hgp
    iStructNamed Hgp'
    try wp_auto
    wp_apply wp_Min ct gp.Term' as %w %Hw
    try wp_auto
    iapply HΦ; ipureintro
    rw [Hw, Hct, Hpf.1]

end proof

end AntCheck
end EtcdGrove
end Perennial
