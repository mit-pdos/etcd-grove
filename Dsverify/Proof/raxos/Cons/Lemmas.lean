/-
Helper lemmas for the consensus laws (package `laws`, internal).
-/
module

public import Dsverify.Proof.raxos.Ghost

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure

namespace consLemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

instance consW_timeless (γ : QNames) (W : World) :
    Timeless (PROP := IProp GF) iprop([∗list] e ∈ W, match e with
      | .init i me ids _ => iprop(ghostMapElem γ.inits (me, i) (DFrac.own 1) () ∗
          [∗list] x ∈ ids, ∃ b, batchReg γ x b)
      | _ => iprop(True)) := by
  refine BigSepL.bigSepL_timeless fun {k e} _ => ?_
  cases e <;> unfold batchReg <;> infer_instance

theorem list_set_self {W : World} {k : Nat} {e : Ev} (hk : W[k]? = some e) : W.set k e = W := by
  apply List.ext_getElem?; intro n; rw [List.getElem?_set]
  split
  · rename_i h; subst h; obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 hk; simp [h1, h2]
  · rfl

theorem spent_le600 {S : List Ticket} {Tix : GMap Ticket (Nat × Nat)} {Cr : GMap Ticket Unit}
    {Rd : GMap Nat Nat}
    (hTix : ∀ t, (Tix !! t).isSome → t ∈ tickets)
    (hCr : ∀ t, (Cr !! t).isSome → ∃ cid n, Tix !! t = some (cid, n) ∧ ∃ m, Rd !! cid = some m ∧ n < m)
    (hNd : S.Nodup) (hS : ∀ t ∈ S, (Cr !! t).isSome) : S.length ≤ 600 := by
  have hsub : ∀ t ∈ S, t ∈ tickets := by
    intro t ht
    obtain ⟨cid, n, h1, -⟩ := hCr t (hS t ht)
    exact hTix t (by rw [h1]; rfl)
  have := (List.subperm_of_subset hNd hsub).length_le
  have e : tickets.length = 600 := by simp [tickets, serverIds, List.length_flatMap]; rfl
  omega

theorem recState_snoc (W : World) (e : Ev) (r i : Int) :
    recState (W ++ [e]) r i = match e with
      | .record r' i' _ _ st' => if r' = r ∧ i' = i then st' else recState W r i
      | _ => recState W r i := by
  unfold recState; rw [List.foldl_append]; rfl

theorem recState_snoc_nonrec {W : World} {e : Ev} (h : ∀ r i s v st, e ≠ .record r i s v st)
    (r i : Int) : recState (W ++ [e]) r i = recState W r i := by
  rw [recState_snoc]
  cases e with
  | record r' i' s' v' st' => exact absurd rfl (h r' i' s' v' st')
  | _ => rfl

theorem evIn_mem (γ : QNames) (q : Qp) (W : World) (e : Ev) :
    ⊢@{IProp GF} monoListAuthOwn γ.hist q W -∗ evIn γ e -∗ ⌜e ∈ W⌝ := by
  iintro Ha He
  unfold evIn
  icases He with ⟨%Wa, #Hla, %Hma⟩
  ihave %Hpa := mono_list_auth_lb_valid γ.hist q W Wa $$ Ha Hla
  ipureintro; exact Hpa.2.subset Hma

theorem evIns_mem (γ : QNames) (W : World) (es : List Ev) :
    ⊢@{IProp GF} monoListAuthOwn γ.hist 1 W -∗ ([∗list] e' ∈ es, evIn γ e') -∗
      monoListAuthOwn γ.hist 1 W ∗ ⌜∀ e' ∈ es, e' ∈ W⌝ := by
  induction es with
  | nil => iintro Ha -; iframe; ipureintro; simp
  | cons e es ih =>
    iintro Ha Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨He, Hes⟩
    ihave %h := evIn_mem γ 1 W e $$ Ha He
    ihave ⟨Ha, %hs⟩ := ih $$ Ha Hes
    iframe
    ipureintro
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h
    · exact hs e' he'


instance confIs_timeless (γ : QNames) (c : QConf) : Timeless (confIs (GF := GF) γ c) := by
  unfold confIs; infer_instance

/-- The history's disjunct of `consInv`. -/
abbrev histOk (γ : QNames) (W : World) : IProp GF :=
  iprop(⌜W = []⌝ ∨ ∃ c : QConf, confIs γ c ∗ ⌜c.ok ∧ Reach (c.n : Int) (c.ep : Int) W⌝)

theorem confIs_agree (γ : QNames) (c1 c2 : QConf) :
    ⊢@{IProp GF} confIs γ c1 -∗ confIs γ c2 -∗ ⌜c1 = c2⌝ := by
  unfold confIs
  iintro H1 H2
  ihave %h := ghostMapElem_agree $$ H1 H2
  ipureintro; exact h

theorem conf_n_pos {c : QConf} (hc : c.ok) : 1 ≤ (c.n : Int) := by
  rcases hc.1 with h | h <;> omega

/-- With the configuration `c`, the history is reachable for `c`. -/
theorem hist_reach (γ : QNames) (W : World) (c : QConf) :
    ⊢@{IProp GF} histOk γ W -∗ confIs γ c -∗ ⌜Reach (c.n : Int) (c.ep : Int) W⌝ := by
  iintro Hh Hc
  icases Hh with (%hW | ⟨%c', Hc', %hc'⟩)
  · ipureintro; subst hW; exact Reach.nil
  · ihave %he := confIs_agree γ c c' $$ Hc Hc'
    ipureintro; subst he; exact hc'.2

/-- A nonempty history is reachable for the chosen configuration. -/
theorem hist_reach_mem (γ : QNames) (W : World) (e : Ev) (he : e ∈ W) :
    ⊢@{IProp GF} histOk γ W -∗ ∃ c : QConf, confIs γ c ∗ ⌜c.ok ∧ Reach (c.n : Int) (c.ep : Int) W⌝ := by
  iintro Hh
  icases Hh with (%hW | H)
  · subst hW; simp at he
  · iexact H

/-- The leader's evidence, against the history. -/
theorem leadEv_ok (γ : QNames) (c : QConf) (W : World) (i me : Int) (lead : Bool) :
    ⊢@{IProp GF} monoListAuthOwn γ.hist 1 W -∗ (if lead then leadEv γ c i me else iprop(True)) -∗
      ⌜lead = true → leaderOk Ev.decide (c.n : Int) (c.ep : Int) W i me⌝ := by
  cases lead with
  | false =>
    iintro - -
    ipureintro; intro h; cases h
  | true =>
    simp only [ite_true]
    iintro Ha Hl
    unfold leadEv
    icases Hl with (%h | ⟨%p, Hd, %hp⟩)
    · ipureintro; intro _; exact Or.inl h
    · unfold decided
      ihave %hm := evIn_mem γ 1 W _ $$ Ha Hd
      ipureintro; intro _
      exact Or.inr ⟨hp.1, p, hm, by simpa using hp.2.1, hp.2.2⟩

/-- Every step of the empty history is an `init`. -/
theorem step_nil {n e : Int} {ev : Ev} (h : Step n e [] ev) :
    ∃ i me ids lead, ev = .init i me ids lead := by
  cases h <;> simp_all

end consLemmas

end Perennial.raxos
