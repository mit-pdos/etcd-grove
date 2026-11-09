/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__Violated`.

`Violated` loops over the package variable `Invariants`, whose contents the package fact gives
(`etcdraftInit`, `Base.lean`): the seven named closures of `Closures.lean`. Each closure calls its
`State` method (`wp_invHolds`, from the methods' specs); the transcription folds over `invariants`
(`Tla/Invariants.lean`), stopping at the first violated (`vstep`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__Violated
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__LogInv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__MoreThanOneLeaderInv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__ElectionSafetyInv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__LogMatchingInv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__QuorumLogInv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__LeaderCompletenessInv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__CommittedIsDurableInv

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

/-! ## The transcription's fold -/

/-- One invariant of `State.violated`'s fold: a violation found stays, else the invariant is
evaluated. -/
def vstep (st : State) (acc : Option String) (inv : String × (State → EvalM Bool)) :
    EvalM (Option String) := do
  match acc with
  | some v => return some v
  | none => return if (← inv.2 st) then none else some inv.1

theorem violated_eq (st : State) : st.violated = invariants.foldlM (vstep st) none := rfl

/-- A violation found stays. -/
theorem vfold_some (st : State) :
    ∀ (l : List (String × (State → EvalM Bool))) (v : String), l.foldlM (vstep st) (some v) = .ok (some v)
  | [], _ => rfl
  | _ :: l, v => by rw [List.foldlM_cons]; exact vfold_some st l v

/-- One step of the fold: the first `n` invariants hold, the whole fold gives `r`, so the `n`-th
evaluates (to `c`): `false` makes it `r`'s violation, `true` passes the first `n + 1`. -/
theorem vfold_step (st : State) (l : List (String × (State → EvalM Bool))) (n : Nat)
    (inv : String × (State → EvalM Bool)) (r : Option String)
    (hy : l[n]? = some inv) (h1 : (l.take n).foldlM (vstep st) none = .ok none)
    (h : l.foldlM (vstep st) none = .ok r) :
    ∃ c, inv.2 st = .ok c ∧ (c = false → r = some inv.1) ∧
      (c = true → (l.take (n + 1)).foldlM (vstep st) none = .ok none) := by
  have hn : n < l.length := (List.getElem?_eq_some_iff.1 hy).1
  have hyn : l[n] = inv := (List.getElem?_eq_some_iff.1 hy).2
  have hl : l = l.take n ++ inv :: l.drop (n + 1) := by
    conv => lhs; rw [← List.take_append_drop n l]
    rw [List.drop_eq_getElem_cons hn, hyn]
  rw [hl, List.foldlM_append, h1] at h
  simp only [bind, Except.bind, List.foldlM_cons] at h
  cases hc : inv.2 st with
  | error e => simp only [vstep, hc, bind, Except.bind] at h; cases h
  | ok c =>
    refine ⟨c, rfl, fun hf => ?_, fun ht => ?_⟩
    · subst hf
      simp only [vstep, hc, bind, Except.bind, Pure.pure, Except.pure, Bool.false_eq_true, ite_false] at h
      rw [vfold_some] at h; cases h; rfl
    · rw [List.take_add_one, hy, Option.toList_some, List.foldlM_append, h1]
      subst ht
      simp only [vstep, hc, bind, Except.bind, Pure.pure, Except.pure, ite_true, List.foldlM_cons,
        List.foldlM_nil]

/-- The end of the fold: every invariant held. -/
theorem vfold_end (st : State) (l : List (String × (State → EvalM Bool))) (n : Nat) (r : Option String)
    (hn : l.length ≤ n) (h1 : (l.take n).foldlM (vstep st) none = .ok none)
    (h : l.foldlM (vstep st) none = .ok r) : r = none := by
  rw [List.take_of_length_le hn, h] at h1
  cases h1; rfl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- A closure of `Invariants` computes `ev` (where it is defined, under the invariants' premises). -/
def holdsSpec (f : GoFunc) (ev : State → EvalM Bool) : Prop :=
  ∀ (p : Loc) (st : State) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗
      ⌜(∀ i ∈ st.server, ((st.s i).log.length : Int) < 2 ^ 63 - 1) ∧
        (∀ i ∈ st.server, (st.getConfig i).length < 2 ^ 62) ∧ ev st = .ok b⌝ }}
    (App (Val #f) (Val #p))
  {{ RET #b; True }}

-- A closure calls its method, whose spec gives the result (`hspec`, applied to `p st`, then the
-- result if the method's spec takes it; `hpre` its pure premise; hygiene off: it names the proof's
-- hypotheses).
set_option hygiene false in
local macro "holds_tac" hval:ident hspec:term "," hpre:term : tactic => `(tactic| (
    intro p st b
    wp_start as ⟨#Hst, %Hpre⟩
    rw [$hval:ident]
    wp_auto
    wp_apply ($hspec:term) $$ [Hst]
    · iframe Hst; ipureintro; exact $hpre
    try wp_auto
    iapply HΦ; ipureintro; trivial))

-- The same for a method without `EvalM` (its result `x`, `pure x` the closure's).
set_option hygiene false in
local macro "holds_pure_tac" hval:ident hspec:term : tactic => `(tactic| (
    intro p st b
    wp_start as ⟨#Hst, %Hpre⟩
    obtain ⟨-, -, hb⟩ := Hpre
    cases hb
    rw [$hval:ident]
    wp_auto
    wp_apply ($hspec:term) $$ [Hst]
    · iframe Hst
    try wp_auto
    iapply HΦ; ipureintro; trivial))

theorem wp_invHolds (wp_LogInv : State.LogInv.spec (GF := GF) (hG := hG))
    (wp_MoreThanOneLeaderInv : State.MoreThanOneLeaderInv.spec (GF := GF) (hG := hG))
    (wp_ElectionSafetyInv : State.ElectionSafetyInv.spec (GF := GF) (hG := hG))
    (wp_LogMatchingInv : State.LogMatchingInv.spec (GF := GF) (hG := hG))
    (wp_QuorumLogInv : State.QuorumLogInv.spec (GF := GF) (hG := hG))
    (wp_LeaderCompletenessInv : State.LeaderCompletenessInv.spec (GF := GF) (hG := hG))
    (wp_CommittedIsDurableInv : State.CommittedIsDurableInv.spec (GF := GF) (hG := hG))
    (k : Nat) (v : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Invariant)
    (ev : String × (State → EvalM Bool))
    (hv : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.invariantsV[k]? = some v)
    (hev : invariants[k]? = some ev) :
    holdsSpec (GF := GF) (hG := hG) v.Holds' ev.2 ∧ strRel v.Name' ev.1 := by
  have hk : k < 7 := (List.getElem?_eq_some_iff.1 hev).1
  open github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft in
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [invariantsV, invariants, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hv hev <;> subst hv hev <;> refine ⟨?_, by dsimp only; unfold strRel; decide⟩
  · holds_tac logInvV_val (wp_LogInv p st b), Hpre.2.2
  · holds_pure_tac moreThanOneLeaderInvV_val (wp_MoreThanOneLeaderInv p st)
  · intro p st b
    wp_start as ⟨#Hst, %Hpre⟩
    obtain ⟨hlog, -, hb⟩ := Hpre
    cases hb
    rw [electionSafetyInvV_val]
    wp_auto
    wp_apply (wp_ElectionSafetyInv p st) $$ [Hst]
    · iframe Hst; ipureintro; exact hlog
    try wp_auto
    iapply HΦ; ipureintro; trivial
  · intro p st b
    wp_start as ⟨#Hst, %Hpre⟩
    obtain ⟨hlog, -, hb⟩ := Hpre
    cases hb
    rw [logMatchingInvV_val]
    wp_auto
    wp_apply (wp_LogMatchingInv p st) $$ [Hst]
    · iframe Hst; ipureintro; exact hlog
    try wp_auto
    iapply HΦ; ipureintro; trivial
  · holds_tac quorumLogInvV_val (wp_QuorumLogInv p st b), ⟨Hpre.2.1, Hpre.2.2⟩
  · holds_tac leaderCompletenessInvV_val (wp_LeaderCompletenessInv p st b), ⟨Hpre.1, Hpre.2.2⟩
  · holds_pure_tac committedIsDurableInvV_val (wp_CommittedIsDurableInv p st)

theorem State.Violated.wp_proof (wp_LogInv : State.LogInv.spec (GF := GF) (hG := hG))
    (wp_MoreThanOneLeaderInv : State.MoreThanOneLeaderInv.spec (GF := GF) (hG := hG))
    (wp_ElectionSafetyInv : State.ElectionSafetyInv.spec (GF := GF) (hG := hG))
    (wp_LogMatchingInv : State.LogMatchingInv.spec (GF := GF) (hG := hG))
    (wp_QuorumLogInv : State.QuorumLogInv.spec (GF := GF) (hG := hG))
    (wp_LeaderCompletenessInv : State.LeaderCompletenessInv.spec (GF := GF) (hG := hG))
    (wp_CommittedIsDurableInv : State.CommittedIsDurableInv.spec (GF := GF) (hG := hG)) :
    State.Violated.spec (GF := GF) (hG := hG) := by
  intro p st r
  wp_start as ⟨#Hst, %Hpre⟩
  obtain ⟨hlog, hcfg, hr⟩ := Hpre
  rw [violated_eq] at hr
  have Hacc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ⊢
      github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.etcdraftInit (GF := GF) :=
    isPkgInit_access (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft
  ihave #HI := Hacc $$ Hpkg
  iunfold github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.etcdraftInit at HI
  icases HI with ⟨%sl, #Hinv, #Hsl⟩
  ihave %Hsllen := ownSlice_len $$ Hsl
  wp_auto
  have hlen7 : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.invariantsV.length = 7 := rfl
  have hlen7' : invariants.length = 7 := rfl
  ihave IH : iprop(∃ (n : w64) (x : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Invariant),
      "i" ∷ i_ptr ↦ n ∗ "inv" ∷ inv_ptr ↦ x ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        (invariants.take (sint.nat n)).foldlM (vstep st) none = .ok none⌝)
      $$ [i inv]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl⟩
  wp_for IH
  obtain ⟨hn0, hn1, hnt⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.invariantsV.length := by
      rw [Hsllen.1]; word
    obtain ⟨v, Hv⟩ : ∃ v, github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.invariantsV[sint.nat n]? = some v :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hlt' : sint.nat n < invariants.length := by rw [hlen7']; rw [hlen7] at Hlt; exact Hlt
    obtain ⟨ev, Hev⟩ : ∃ ev, invariants[sint.nat n]? = some ev := ⟨_, List.getElem?_eq_getElem Hlt'⟩
    obtain ⟨hhold, hname⟩ := wp_invHolds wp_LogInv wp_MoreThanOneLeaderInv wp_ElectionSafetyInv
      wp_LogMatchingInv wp_QuorumLogInv wp_LeaderCompletenessInv wp_CommittedIsDurableInv (sint.nat n) v ev Hv Hev
    obtain ⟨c, hc, hcf, hct⟩ := vfold_step st invariants (sint.nat n) ev r Hev hnt hr
    have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index sl (sint.Z n) _ DFrac.discard v hn0 $$ [Hsl] as -
    · isplitr
      · iexact Hsl
      ipureintro; exact Hv
    try wp_auto
    wp_apply (hhold p st c) $$ [Hst]
    · iframe Hst; ipureintro; exact ⟨hlog, hcfg, hc⟩
    cases c
    · -- violated: its name
      try wp_auto
      wp_for_post
      try wp_auto
      iapply HΦ
      ipureintro
      rw [hcf rfl]; exact hname
    · try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [hn1']; exact hct rfl
  · -- none violated
    have hne : invariants.length ≤ sint.nat n := by
      rw [hlen7', ← hlen7, Hsllen.1]; word
    have hrn := vfold_end st invariants (sint.nat n) r hne hnt hr
    try wp_auto
    iapply HΦ; ipureintro; rw [hrn]; exact strRel_empty

end proof

end Etcdraft
end EtcdGrove
end Perennial
