/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Model/Cut.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2 (notes/l2-design.md §5, notes/prove-s2-d.md): the maximal valid cut of the nodes' predicted
futures, abstractly. Nodes `ν` (a finite list `Ns` of them), per-node event lists, a state `σ`,
an event's guard `ok s n e` and effect `ap s n e`, an invariant `I`. A configuration is the state
with the remaining lists; a step runs some node's next event if it is ok. Under **locality**
(`Diamond`: two different nodes' ok events stay ok after each other and commute) every
configuration has exactly one normal form (`nf_unique`): the run of the maximal valid cut, whose
final state does not depend on the interleaving. A step of the configuration keeps the normal
form (`nfOf_step`: the stability of the cut under a real event that was predicted).
-/
module

public import Init

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

namespace Cut

variable {ν σ ε α : Type} [DecidableEq ν]

/-- `f` with `n`'s value replaced (core has no `upd`). -/
def upd (f : ν → α) (n : ν) (v : α) : ν → α := fun m => if m = n then v else f m

theorem upd_same (f : ν → α) (n : ν) (v : α) : upd f n v n = v := by simp [upd]
theorem upd_ne (f : ν → α) {n m : ν} (v : α) (h : m ≠ n) : upd f n v m = f m := by simp [upd, h]
theorem upd_comm (f : ν → α) {n m : ν} (v w : α) (h : n ≠ m) :
    upd (upd f n v) m w = upd (upd f m w) n v := by
  funext k; unfold upd; by_cases a : k = m <;> by_cases b : k = n <;> simp_all

/-- A configuration: the state and every node's remaining predicted events. -/
abbrev Conf (ν σ ε : Type) := σ × (ν → List ε)

section
variable (Ns : List ν) (ok : σ → ν → ε → Prop) (ap : σ → ν → ε → σ)

/-- One step: a node of `Ns` runs its next event, which is ok. -/
def StepN (n : ν) (c c' : Conf ν σ ε) : Prop :=
  n ∈ Ns ∧ ∃ e rest, c.2 n = e :: rest ∧ ok c.1 n e ∧
    c' = (ap c.1 n e, upd c.2 n rest)

def Step (c c' : Conf ν σ ε) : Prop := ∃ n, StepN Ns ok ap n c c'

/-- Runs (the reflexive-transitive closure). -/
inductive Star : Conf ν σ ε → Conf ν σ ε → Prop
  | refl (c) : Star c c
  | head {c c' d} : Step Ns ok ap c c' → Star c' d → Star c d

def Stuck (c : Conf ν σ ε) : Prop := ∀ c', ¬ Step Ns ok ap c c'

/-- `d` is the end of a run from `c` where no node can go on: the maximal valid cut's run. -/
def NF (c d : Conf ν σ ε) : Prop := Star Ns ok ap c d ∧ Stuck Ns ok ap d

/-- The events left in the nodes' lists. -/
def measure (c : Conf ν σ ε) : Nat := (Ns.map (fun n => (c.2 n).length)).sum

end

theorem sum_lt {Ns : List ν} {f g : ν → Nat} {n : ν} (hn : n ∈ Ns) (hlt : g n < f n)
    (hle : ∀ m, m ≠ n → g m = f m) : (Ns.map g).sum < (Ns.map f).sum := by
  induction Ns with
  | nil => simp at hn
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hle' : ∀ l : List ν, (l.map g).sum ≤ (l.map f).sum := by
      intro l; induction l with
      | nil => simp
      | cons b l ih2 =>
        simp only [List.map_cons, List.sum_cons]
        have : g b ≤ f b := by
          by_cases e : b = n
          · subst e; omega
          · rw [hle b e]; omega
        omega
    by_cases e : a = n
    · subst e; have := hle' l; omega
    · have hn' : n ∈ l := by simp at hn; rcases hn with h | h; exact absurd h.symm e; exact h
      have := ih hn'; rw [hle a e]; omega

section
variable {Ns : List ν} {ok : σ → ν → ε → Prop} {ap : σ → ν → ε → σ}

theorem StepN.measure_lt {n : ν} {c c' : Conf ν σ ε} (h : StepN Ns ok ap n c c') :
    measure Ns c' < measure Ns c := by
  obtain ⟨hn, e, rest, he, -, rfl⟩ := h
  unfold measure
  apply sum_lt hn
  · simp [he, upd_same]
  · intro m hm; simp [upd, hm]

theorem Step.measure_lt {c c' : Conf ν σ ε} (h : Step Ns ok ap c c') :
    measure Ns c' < measure Ns c := let ⟨_, h⟩ := h; h.measure_lt

/-- A step is determined by its node. -/
theorem StepN.det {n : ν} {c c1 c2 : Conf ν σ ε} (h1 : StepN Ns ok ap n c c1)
    (h2 : StepN Ns ok ap n c c2) : c1 = c2 := by
  obtain ⟨-, e1, r1, he1, -, rfl⟩ := h1
  obtain ⟨-, e2, r2, he2, -, rfl⟩ := h2
  rw [he1] at he2; cases he2; rfl

theorem Star.trans {c d f : Conf ν σ ε} (h1 : Star Ns ok ap c d) (h2 : Star Ns ok ap d f) :
    Star Ns ok ap c f := by
  induction h1 with
  | refl => exact h2
  | head s _ ih => exact .head s (ih h2)

/-- Every configuration has a normal form (the lists are finite). -/
theorem nf_exists : ∀ (c : Conf ν σ ε), ∃ d, NF Ns ok ap c d := by
  intro c
  induction hm : measure Ns c using Nat.strongRecOn generalizing c with
  | _ m ih =>
    by_cases hs : Stuck Ns ok ap c
    · exact ⟨c, .refl c, hs⟩
    · have : ∃ c', Step Ns ok ap c c' :=
        Classical.byContradiction fun h' => hs fun c' hc => h' ⟨c', hc⟩
      obtain ⟨c', hc'⟩ := this
      obtain ⟨d, hd1, hd2⟩ := ih _ (hm ▸ hc'.measure_lt) c' rfl
      exact ⟨d, .head hc' hd1, hd2⟩

/-- The normal form. -/
def nfOf (Ns : List ν) (ok : σ → ν → ε → Prop) (ap : σ → ν → ε → σ) (c : Conf ν σ ε) :
    Conf ν σ ε :=
  Classical.choose (nf_exists (Ns := Ns) (ok := ok) (ap := ap) c)

theorem nfOf_spec (c : Conf ν σ ε) : NF Ns ok ap c (nfOf Ns ok ap c) :=
  Classical.choose_spec (nf_exists c)

end

/-- **Locality**, the hypothesis: an invariant kept by every ok event, and two ok events of
different nodes stay ok after each other and commute. -/
structure Diamond (ok : σ → ν → ε → Prop) (ap : σ → ν → ε → σ) (I : σ → Prop) : Prop where
  inv : ∀ s n e, I s → ok s n e → I (ap s n e)
  ok_after : ∀ s n1 e1 n2 e2, I s → n1 ≠ n2 → ok s n1 e1 → ok s n2 e2 → ok (ap s n1 e1) n2 e2
  comm : ∀ s n1 e1 n2 e2, I s → n1 ≠ n2 → ok s n1 e1 → ok s n2 e2 →
    ap (ap s n1 e1) n2 e2 = ap (ap s n2 e2) n1 e1

section
variable {Ns : List ν} {ok : σ → ν → ε → Prop} {ap : σ → ν → ε → σ} {I : σ → Prop}

theorem Step.inv (hD : Diamond ok ap I) {c c' : Conf ν σ ε} (h : Step Ns ok ap c c')
    (hI : I c.1) : I c'.1 := by
  obtain ⟨n, -, e, r, -, hok, rfl⟩ := h
  exact hD.inv _ _ _ hI hok

theorem Star.inv (hD : Diamond ok ap I) {c d : Conf ν σ ε} (h : Star Ns ok ap c d)
    (hI : I c.1) : I d.1 := by
  induction h with
  | refl => exact hI
  | head s _ ih => exact ih (s.inv hD hI)

/-- The diamond on configurations. -/
theorem diamond_conf (hD : Diamond ok ap I) {n1 n2 : ν} {c c1 c2 : Conf ν σ ε} (hI : I c.1)
    (hne : n1 ≠ n2) (h1 : StepN Ns ok ap n1 c c1) (h2 : StepN Ns ok ap n2 c c2) :
    ∃ c3, StepN Ns ok ap n2 c1 c3 ∧ StepN Ns ok ap n1 c2 c3 := by
  obtain ⟨hn1, e1, r1, he1, hok1, rfl⟩ := h1
  obtain ⟨hn2, e2, r2, he2, hok2, rfl⟩ := h2
  refine ⟨(ap (ap c.1 n1 e1) n2 e2, upd (upd c.2 n1 r1) n2 r2),
    ⟨hn2, e2, r2, by simp [upd, Ne.symm hne, he2],
      hD.ok_after _ _ _ _ _ hI hne hok1 hok2, rfl⟩,
    ⟨hn1, e1, r1, by simp [upd, hne, he1],
      hD.ok_after _ _ _ _ _ hI (Ne.symm hne) hok2 hok1, ?_⟩⟩
  simp only
  rw [hD.comm _ _ _ _ _ hI hne hok1 hok2, upd_comm _ _ _ (Ne.symm hne)]

/-- **The normal form is unique** (the maximal valid cut's final configuration does not depend
on the interleaving). -/
theorem nf_unique (hD : Diamond ok ap I) : ∀ (c : Conf ν σ ε) {d1 d2 : Conf ν σ ε}, I c.1 →
    NF Ns ok ap c d1 → NF Ns ok ap c d2 → d1 = d2 := by
  intro c
  induction hm : measure Ns c using Nat.strongRecOn generalizing c with
  | _ m ih =>
    intro d1 d2 hI ⟨r1, s1⟩ ⟨r2, s2⟩
    cases r1 with
    | refl =>
      cases r2 with
      | refl => rfl
      | head st _ => exact absurd st (s1 _)
    | head st1 rr1 =>
      cases r2 with
      | refl => exact absurd st1 (s2 _)
      | head st2 rr2 =>
        rename_i c1 c2
        obtain ⟨n1, h1⟩ := st1
        obtain ⟨n2, h2⟩ := st2
        have m1 : measure Ns c1 < m := hm ▸ h1.measure_lt
        have m2 : measure Ns c2 < m := hm ▸ h2.measure_lt
        have I1 : I c1.1 := Step.inv hD ⟨n1, h1⟩ hI
        have I2 : I c2.1 := Step.inv hD ⟨n2, h2⟩ hI
        by_cases hn : n1 = n2
        · subst hn
          have := h1.det h2; subst this
          exact ih _ m1 c1 rfl I1 ⟨rr1, s1⟩ ⟨rr2, s2⟩
        · obtain ⟨c3, h13, h23⟩ := diamond_conf hD hI hn h1 h2
          obtain ⟨d3, r3, s3⟩ := nf_exists (Ns := Ns) (ok := ok) (ap := ap) c3
          have e1 := ih _ m1 c1 rfl I1 ⟨rr1, s1⟩ ⟨.head ⟨n2, h13⟩ r3, s3⟩
          have e2 := ih _ m2 c2 rfl I2 ⟨rr2, s2⟩ ⟨.head ⟨n1, h23⟩ r3, s3⟩
          rw [e1, e2]

theorem nfOf_eq (hD : Diamond ok ap I) {c d : Conf ν σ ε} (hI : I c.1) (h : NF Ns ok ap c d) :
    nfOf Ns ok ap c = d :=
  nf_unique hD c hI (nfOf_spec c) h

/-- **Stability**: a configuration's step (a real event that was its node's next predicted one,
ok now) keeps the normal form. -/
theorem nfOf_step (hD : Diamond ok ap I) {c c' : Conf ν σ ε} (hI : I c.1)
    (h : Step Ns ok ap c c') : nfOf Ns ok ap c' = nfOf Ns ok ap c := by
  have ⟨r, s⟩ := nfOf_spec (Ns := Ns) (ok := ok) (ap := ap) c'
  exact (nfOf_eq hD hI ⟨.head h r, s⟩).symm

/-- The node `n`'s next event `e`, ok now, is a step. -/
theorem step_of_head {c : Conf ν σ ε} {n : ν} {e : ε} {rest : List ε} (hn : n ∈ Ns)
    (he : c.2 n = e :: rest) (hok : ok c.1 n e) :
    Step Ns ok ap c (ap c.1 n e, upd c.2 n rest) :=
  ⟨n, hn, e, rest, he, hok, rfl⟩

/-- A map of states that commutes with every event and keeps `ok` (the change of an
unpredicted value no guard reads) commutes with the normal form. -/
theorem nfOf_map (hD : Diamond ok ap I) (f : σ → σ) (J : σ → Prop)
    (hJ : ∀ s n e, J s → ok s n e → J (ap s n e))
    (hok : ∀ s n e, J s → (ok (f s) n e ↔ ok s n e))
    (hap : ∀ s n e, J s → ok s n e → ap (f s) n e = f (ap s n e))
    {c : Conf ν σ ε} (hJ0 : J c.1) (hI : I (f c.1)) :
    nfOf Ns ok ap (f c.1, c.2) = (f (nfOf Ns ok ap c).1, (nfOf Ns ok ap c).2) := by
  apply nfOf_eq hD hI
  obtain ⟨r, s⟩ := nfOf_spec (Ns := Ns) (ok := ok) (ap := ap) c
  -- map the run
  have run : ∀ {c d : Conf ν σ ε}, Star Ns ok ap c d → J c.1 →
      Star Ns ok ap (f c.1, c.2) (f d.1, d.2) ∧ J d.1 := by
    intro c d h hJc
    induction h with
    | refl => exact ⟨.refl _, hJc⟩
    | head st _ ih =>
      obtain ⟨n, hn, e, rest, he, hok', rfl⟩ := st
      obtain ⟨ih1, ih2⟩ := ih (hJ _ _ _ hJc hok')
      refine ⟨.head ⟨n, hn, e, rest, he, (hok _ _ _ hJc).mpr hok', ?_⟩ ih1, ih2⟩
      simp only [hap _ _ _ hJc hok']
  obtain ⟨r', hJd⟩ := run r hJ0
  refine ⟨r', fun c' ⟨n, hn, e, rest, he, hok', _⟩ => s _ ⟨n, hn, e, rest, he,
    (hok _ _ _ hJd).mp hok', rfl⟩⟩

end

end Cut

end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
