/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `State.Made` (B 496-499), the template of an action proof (`notes/antithesis-check-design.md` §10, "How to prove an action").
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Made
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setPre
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

theorem State.Made.wp_proof
    (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_setPre : setPre.spec (GF := GF) (hG := hG)) :
    State.Made.spec (GF := GF) (hG := hG) := by
  intro p s n e ev o
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %_Hb, %Ho⟩
  -- read the state: its struct's fields, each field's representation, its shape
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  -- `s.Undo[n]`, the Lean's `s.undo[n]!`
  icases undoRO_at g.Undo' s.undo n ⟨Hn, by rw [HWf.len_undo]; exact Hlt⟩ $$ HUndo with ⟨%u, #Hua, #Hu⟩
  unfold State.made at Ho
  wp_auto
  wp_apply wp_load_at _ _ u Hn $$ [Hua]
  · iexact Hua
  cases hu : s.undo[sint.nat n]! with
  | none =>
    -- `NoWrite`: not enabled
    rw [hu] at Ho
    cases Ho
    iunfold preRO at Hu
    icases Hu with %Hnull
    subst Hnull
    wp_auto
    iapply HΦ
    iunfold succOwn
    ipureintro; rfl
  | some pu =>
    rw [hu] at Ho
    cases Ho
    iunfold preRO at Hu
    icases Hu with ⟨%gp, #Hgp, #Hpre⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgp
    wp_if_destruct
    · exact absurd rfl Hnn
    wp_apply wp_load_at _ _ u Hn $$ [Hua]
    · iexact Hua
    try wp_auto
    wp_apply wp_clone p s $$ [Hs] as %q Hq
    · iexact Hs
    -- `&nu`, never written again: read-only, holding `{ pu with made := true }`
    ipersist nu
    icases Hpre with ⟨%Hpf, #Hsuf, #Hms, #Hvs, #Hacks⟩
    ihave #Hnu : preRO nu_ptr (some { pu with made := true }) $$ []
    · iunfold preRO
      iexists _
      iframe nu Hsuf Hms Hvs Hacks
      ipureintro
      exact ⟨Hpf.1, Hpf.2.1, Hpf.2.2.1, Hpf.2.2.2.1, Hpf.2.2.2.2.1, Hpf.2.2.2.2.2.1, Hpf.2.2.2.2.2.2.1, rfl⟩
    wp_apply wp_setPre g.Undo' s.undo n nu_ptr _ $$ [HUndo Hnu] as %out #Hout
    · iframe HUndo Hnu; ipureintro; exact ⟨Hn, by rw [HWf.len_undo]; exact Hlt⟩
    try wp_auto
    -- `ns.Undo = ...`: the Lean's `{ s with undo := s.undo.set n (some { pu with made := true }) }`
    wp_apply wp_set_undo q s out (s.undo.set (sint.nat n) (some { pu with made := true }))
      (by rw [List.length_set, HWf.len_undo]) $$ [Hq Hout] as Hq
    · iframe Hq Hout
    try wp_auto
    iapply HΦ
    iunfold succOwn
    isplitr
    · ipureintro; rfl
    iexact Hq

end proof

end AntCheck
end EtcdGrove
end Perennial
