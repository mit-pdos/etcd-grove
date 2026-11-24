/-
Lean-first (no Rocq counterpart). #33 S3b W7 (2026-11-23): the proof of `Run` (`check.go`).

The loop's invariant: after `n` reports the checker holds `foldlM next` over them, has no verdict
(the Go breaks at one), and its state is within `1 + Σ weight` of them (`CheckLaws.next_within_of`,
from `StepWithin` and `GCWithin`) with the configuration `cfg` (`StepCfg`, `gc_cfg`), so that the
next report meets `Next`'s `BoundedFor` (by `Stream.Bounded`, `Stream.ConfBounded`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.NewChecker
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Checker__Next
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Checker__End
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.CheckLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Init0

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Run.wp_proof
    (wp_NewChecker : NewChecker.spec (GF := GF) (hG := hG))
    (wp_Next : Checker.Next.spec (GF := GF) (hG := hG))
    (wp_End : Checker.End.spec (GF := GF) (hG := hG))
    (step_within : StepWithin) (gc_within : GCWithin) (step_cfg : CheckLaws.StepCfg) :
    Run.spec (GF := GF) (hG := hG) := by
  intro cp cfg sl evs v
  wp_start as ⟨#Hc, #Hevs, %Hcb, %Hsb, %Hcf, %Hrun⟩
  unfold run at Hrun
  obtain ⟨s0, hs0, Hrun⟩ := bind_ok Hrun
  obtain ⟨cF, hcF, Hrun⟩ := bind_ok Hrun
  simp only [pure_ok, Except.ok.injEq] at Hrun
  subst Hrun
  obtain ⟨E, hChE, hE⟩ := Hcf
  have hW0 := init0_within cfg s0 E Hcb hs0
  wp_auto
  wp_apply wp_NewChecker cp cfg s0 $$ [Hc] as %c0 Hc0
  · iframe Hc; ipureintro; exact ⟨Hcb, hs0⟩
  try wp_auto
  iunfold eventsRO at Hevs
  icases Hevs with ⟨%ps, #Hps, #Hpe⟩
  ihave %Hl := ownSlice_len $$ Hps
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hpe
  ihave IH : iprop(∃ (n : w64) (y : Loc) (ck : Checker),
      "i" ∷ i_ptr ↦ n ∗ "ev" ∷ ev_ptr ↦ y ∗ "Hck" ∷ checkerOwn c0 ck ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        (evs.drop (sint.nat n)).foldlM (fun c ev => c.next ev) ck = .ok cF ∧ ck.done = false ∧
        ck.state.Within (1 + ((evs.take (sint.nat n)).map Event.weight).sum) E ∧ ck.state.cfg = cfg⌝)
      $$ [i ev Hc0]
  · iexists _, _, _
    iframe
    ipureintro
    rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, List.take_zero]
    exact ⟨by word, by word, hcF, rfl, hW0, CheckLaws.init0_cfg hs0⟩
  wp_for IH
  obtain ⟨hn0, hn1, hfold, hdone, hWk, hcfgk⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < ps.length := by rw [Hl.1]; word
    have Hlt' : sint.nat n < evs.length := by omega
    obtain ⟨y', Hy'⟩ : ∃ z, ps[sint.nat n]? = some z := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) ps DFrac.discard y' hn0 $$ [Hps] as -
    · isplitr
      · iexact Hps
      ipureintro; exact Hy'
    try wp_auto
    icases bigSepL2_at _ ps evs (sint.nat n) Hlt' $$ Hpe with ⟨%x, %Hx, #Hex⟩
    rw [Hy'] at Hx; cases Hx
    have hev : evs[sint.nat n]! = evs[sint.nat n] := getElem!_pos evs (sint.nat n) Hlt'
    rw [List.drop_eq_getElem_cons Hlt', List.foldlM_cons] at hfold
    obtain ⟨ck', hnext, hrest⟩ := bind_ok hfold
    have hBF := CheckLaws.run_boundedFor Hlt' Hsb hChE hE hWk hcfgk
    rw [← hev] at hnext hBF
    wp_apply wp_Next c0 ck y' evs[sint.nat n]! ck' $$ [Hck Hex]
    · iframe Hck Hex; ipureintro; exact ⟨fun _ => hBF, hnext⟩
    iintro Hck
    iunfold checkerOwn at Hck
    icases Hck with ⟨%g, Hp, #Hs, #Hv, %Hd⟩
    obtain ⟨gs, gd, gv⟩ := g
    simp only at Hd
    subst Hd
    icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hpn⟩
    icases typedPointsto_split _ _ _ $$ Hp with Hp
    simp only [TypedPointsto.typedPointstoDef, named]
    icases Hp with ⟨State, Done, Verdict, -⟩
    try wp_auto
    ihave Hck : checkerOwn c0 ck' $$ [State Done Verdict]
    · iunfold checkerOwn
      iexists { State' := gs, Done' := ck'.done, Verdict' := gv }
      isplitl [State Done Verdict]
      · iapply typedPointsto_combine _ _ _ Hpn
        simp only [TypedPointsto.typedPointstoDef, named]
        iframe
      iframe Hs Hv
      ipureintro; rfl
    cases hd' : ck'.done
    · obtain ⟨hW', hcfg'⟩ := CheckLaws.run_step_of step_within gc_within step_cfg Hlt' Hsb hChE hdone hWk
        hcfgk (by rw [← hev]; exact hnext) hd'
      wp_pures
      wp_for_post
      iframe
      ipureintro
      have h1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [h1]
      exact ⟨by word, by word, hrest, hd', hW', hcfg'⟩
    · wp_pures
      wp_for_post
      rw [CheckLaws.foldlM_next_of_done hd'] at hrest
      cases hrest
      wp_apply wp_End c0 _ $$ [Hck] as %r ⟨#Hr, -⟩
      · iframe Hck; ipureintro; intro h; rw [hd'] at h; cases h
      try wp_auto
      iapply HΦ
      iexact Hr
  · have hnx : sint.nat n = evs.length := by have := Hl.1; word
    rw [hnx, List.drop_length] at hfold
    cases hfold
    rw [hnx] at hWk
    try wp_auto
    wp_apply wp_End c0 _ $$ [Hck] as %r ⟨#Hr, -⟩
    · iframe Hck; ipureintro; intro _; exact CheckLaws.run_bounded Hsb hWk
    try wp_auto
    iapply HΦ
    iexact Hr

end proof

end AntCheck
end EtcdGrove
end Perennial
