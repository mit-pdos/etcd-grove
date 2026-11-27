/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/X/Pure.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit X: the executor's pure facts

* `Stable s s'`: the committed (or executed) copies of `s` are in `s'` with the same commands,
  `Seq`, `Deps`, `Base` (what the executor needs across its lock releases; the law that gives it
  is request H-X-1).
* The transfer of Tarjan's invariants (`TInv`, `LInv`, `Post`) along `Stable`.
* `execGuard_of`: a popped component, executed in its key order, satisfies the execution event's
  guard at each member.
* `stepExec_ok`: the shape of an execution step's result.
-/
module

public import Dsverify.Proof.gryff.Model.StepExec
public import Dsverify.Proof.gryff.Replica.Tarjan
public import Dsverify.Proof.gryff.Replica2.State

@[expose] public section

noncomputable section

namespace Perennial.gryff.X

open Perennial.gryff.model
open Perennial.gryff.replica (Node sccStep keyLt XClosed boxList TInv LInv Post TState Reach
  mem_boxList)

/-! ## Stability of committed copies -/

/-- The committed or executed copies of `s` are still committed or executed in `s'`, with the
same commands, `Seq`, `Deps` and `Base`. -/
def Stable (s s' : RState) : Prop :=
  ∀ n c, committedCopy s n = some c → ∃ c', committedCopy s' n = some c' ∧
    c'.cmds = c.cmds ∧ c'.seq = c.seq ∧ c'.deps = c.deps ∧ c'.base = c.base

theorem Stable.refl (s : RState) : Stable s s :=
  fun _ c h => ⟨c, h, rfl, rfl, rfl, rfl⟩

theorem Stable.trans {s1 s2 s3 : RState} (h1 : Stable s1 s2) (h2 : Stable s2 s3) :
    Stable s1 s3 := by
  intro n c hc
  obtain ⟨c2, hc2, a1, a2, a3, a4⟩ := h1 n c hc
  obtain ⟨c3, hc3, b1, b2, b3, b4⟩ := h2 n c2 hc2
  exact ⟨c3, hc3, b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4⟩

theorem Stable.isSome {s s' : RState} (h : Stable s s') {n : Node}
    (hn : (committedCopy s n).isSome) : (committedCopy s' n).isSome := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hn
  obtain ⟨c', hc', -⟩ := h n c hc
  rw [hc']; rfl

theorem depR_mono {s s' : RState} (h : Stable s s') {u w : Node} (hd : depR s u w) :
    depR s' u w := by
  obtain ⟨c, hc, h0, h1, h2, h3⟩ := hd
  obtain ⟨c', hc', -, -, hdeps, -⟩ := h u c hc
  exact ⟨c', hc', h0, h1, h2, by rw [hdeps]; exact h3⟩

theorem depR_back {s s' : RState} (h : Stable s s') {u w : Node}
    (hu : (committedCopy s u).isSome) (hd : depR s' u w) : depR s u w := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hu
  obtain ⟨c', hc', -, -, hdeps, -⟩ := h u c hc
  obtain ⟨c'', hc'', h0, h1, h2, h3⟩ := hd
  rw [hc'] at hc''; cases hc''
  exact ⟨c, hc, h0, h1, h2, by rw [← hdeps]; exact h3⟩

/-- Every node with a committed copy is in the box. -/
theorem committedCopy_box {s : RState} {n : Node} (h : (committedCopy s n).isSome) :
    replica.inBox n := by
  unfold committedCopy at h
  split at h
  · rename_i hb; exact ⟨hb.1, hb.2.1, hb.2.2.1, by have := hb.2.2.2; unfold SLOTS at this; omega⟩
  · simp at h

theorem committedCopy_inst {s : RState} {n : Node} {c : Copy} (h : committedCopy s n = some c) :
    s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c ∧
      (c.status = St.COMMITTED ∨ c.status = St.EXECUTED) := by
  unfold committedCopy at h
  split at h
  · split at h
    · rename_i c' hc'
      split at h
      · cases h; exact ⟨hc', by assumption⟩
      · cases h
    · cases h
  · cases h

theorem executedB_isSome {s : RState} {n : Node} (h : executedB s n = true) :
    (committedCopy s n).isSome := by
  unfold executedB at h
  split at h
  · rename_i c hc; rw [hc]; rfl
  · simp at h

theorem TInv.stable {s s' : RState} (hs : Stable s s') {σ : TState} {G : List Node}
    (hS : ∀ u ∈ σ.S, (committedCopy s u).isSome) (h : TInv (depR s) σ G) :
    TInv (depR s') σ G :=
  h.mono (fun _ _ hd => depR_mono hs hd) (fun u hu _ hd => depR_back hs (hS u hu) hd)

theorem LInv.stable {s s' : RState} (hs : Stable s s') {σ0 σ : TState} {G : List Node}
    {v : Node} {done : Node → Prop} (hS : ∀ u ∈ σ.S, (committedCopy s u).isSome)
    (h : LInv (depR s) σ0 G v done σ) : LInv (depR s') σ0 G v done σ :=
  h.mono (fun _ _ hd => depR_mono hs hd) (fun u hu _ hd => depR_back hs (hS u hu) hd)

theorem Post.stable {s s' : RState} (hs : Stable s s') {σ0 σ : TState} {G : List Node}
    {v : Node} (hS : ∀ u ∈ σ.S, (committedCopy s u).isSome)
    (h : Post (depR s) σ0 G v σ) : Post (depR s') σ0 G v σ :=
  h.mono (fun _ _ hd => depR_mono hs hd) (fun u hu _ hd => depR_back hs (hS u hu) hd)

theorem XClosed.stable {s s' : RState} (hs : Stable s s') {X : List Node}
    (hX : ∀ u ∈ X, (committedCopy s u).isSome) (h : XClosed (depR s) X) :
    XClosed (depR s') X :=
  fun x hx y hd => h x hx y (depR_back hs (hX x hx) hd)

theorem sccStep.stable {s s' : RState} (hs : Stable s s') {X L : List Node}
    (hL : ∀ u ∈ L, (committedCopy s u).isSome) (h : sccStep (depR s) X L) :
    sccStep (depR s') X L := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, fun u hu w hd => h4 u hu w (depR_back hs (hL u hu) hd),
    fun u hu w hw => (h5 u hu w hw).mono (fun _ _ hd => depR_mono hs hd)⟩

/-! ## The execution order -/

/-- The sort key of a node at state `s`: its committed copy's `Seq`, then the node. -/
def keyS (s : RState) (n : Node) : Int × Int × Int :=
  match committedCopy s n with
  | some c => (sint.Z c.seq, n.1, n.2)
  | none => (0, n.1, n.2)

theorem keyS_stable {s s' : RState} (hs : Stable s s') {n : Node}
    (hn : (committedCopy s n).isSome) : keyS s' n = keyS s n := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hn
  obtain ⟨c', hc', -, hseq, -, -⟩ := hs n c hc
  simp only [keyS, hc, hc', hseq]

theorem keyS_of {s : RState} {n : Node} {c : Copy} (h : committedCopy s n = some c) :
    keyS s n = (sint.Z c.seq, n.1, n.2) := by
  simp only [keyS, h]

/-- The copies' leader and slot are their nodes' (the heap's `copyRep` gives it). -/
def LeaderOk (s : RState) : Prop :=
  ∀ n c, committedCopy s n = some c → sint.Z c.leader = n.1 ∧ sint.Z c.slot = n.2

theorem keyAt_eq {s : RState} (hl : LeaderOk s) (n : Node) : keyAt s n = keyS s n := by
  unfold keyAt keyS
  cases hc : committedCopy s n with
  | none => rfl
  | some c =>
    obtain ⟨h1, h2⟩ := hl n c hc
    simp only [h1, h2]

theorem keyLt_irrefl (a : Int × Int × Int) : ¬ keyLt a a := by
  unfold keyLt; omega

theorem keyLt_asymm {a b : Int × Int × Int} (h : keyLt a b) : ¬ keyLt b a := by
  unfold keyLt at *; omega

theorem keyLt_trans {a b c : Int × Int × Int} (h1 : keyLt a b) (h2 : keyLt b c) : keyLt a c := by
  unfold keyLt at *; omega

theorem keyLt_total {a b : Int × Int × Int} (h : a ≠ b) : keyLt a b ∨ keyLt b a := by
  unfold keyLt
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  simp only
  by_cases e1 : a1 = b1
  · by_cases e2 : a2 = b2
    · have e3 : a3 ≠ b3 := fun e3 => h (by rw [e1, e2, e3])
      omega
    · omega
  · omega

theorem keyS_inj {s : RState} {a b : Node} (h : keyS s a = keyS s b) : a = b := by
  unfold keyS at h
  split at h <;> split at h <;> simp only [Prod.mk.injEq] at h <;>
    exact Prod.ext h.2.1 h.2.2

/-- A sort's output (no element less than an earlier one), on distinct nodes, is strictly
sorted by the key. -/
theorem sorted_of_sort (s : RState) (Ls : List Node) (hnd : Ls.Nodup)
    (h : ∀ (i j : Nat) (a b : Node), Ls[i]? = some a → Ls[j]? = some b → i < j →
      ¬ keyLt (keyS s b) (keyS s a)) :
    Ls.Pairwise (fun a b => keyLt (keyS s a) (keyS s b)) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hne : Ls[i] ≠ Ls[j] := (List.pairwise_iff_getElem.1 hnd) i j hi hj hij
  have hn := h i j Ls[i] Ls[j] (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
  rcases keyLt_total (fun e => hne (keyS_inj e)) with h1 | h1
  · exact h1
  · exact absurd h1 hn

/-- In a strictly sorted list without duplicates, the members before position `j` are exactly
those of key below the `j`-th's. -/
theorem mem_take_iff_keyLt {s : RState} {Ls : List Node}
    (hsort : Ls.Pairwise (fun a b => keyLt (keyS s a) (keyS s b))) {j : Nat} {n : Node}
    (hn : Ls[j]? = some n) {u : Node} (hu : u ∈ Ls) :
    u ∈ Ls.take j ↔ keyLt (keyS s u) (keyS s n) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hn
  have hp := List.pairwise_iff_getElem.1 hsort
  constructor
  · intro ht
    obtain ⟨i', hi', he⟩ := List.getElem_of_mem ht
    rw [List.getElem_take] at he
    rw [List.length_take] at hi'
    rw [← he]
    exact hp i' j (by omega) hj (by omega)
  · intro hlt
    rcases Nat.lt_trichotomy i j with h | h | h
    · rw [List.mem_iff_getElem]
      exact ⟨i, by rw [List.length_take]; omega, by rw [List.getElem_take]⟩
    · subst h; exact absurd hlt (keyLt_irrefl _)
    · exact absurd hlt (keyLt_asymm (hp j i hj hi h))

/-! ## The execution event's guard at a popped component's members -/

theorem sccStep_congr {E : Node → Node → Prop} {X X' L : List Node}
    (hX : ∀ u, u ∈ X' ↔ u ∈ X) (h : sccStep E X L) : sccStep E X' L := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, fun u hu hx => h3 u hu ((hX u).1 hx),
    fun u hu w hw => (h4 u hu w hw).imp (fun hx => (hX w).2 hx) id, h5⟩

theorem XClosed_congr {E : Node → Node → Prop} {X X' : List Node}
    (hX : ∀ u, u ∈ X' ↔ u ∈ X) (h : XClosed E X) : XClosed E X' :=
  fun x hx y hd => (hX y).2 (h x ((hX x).1 hx) y hd)

/-- **The guard of the `j`-th execution of a popped component** `Ls` (in key order), after the
executed instances `X` (dependency-closed) and the first `j` members. -/
theorem execGuard_of (s : RState) (X Ls : List Node) (j : Nat) (n : Node)
    (hL : sccStep (depR s) X Ls) (hXc : XClosed (depR s) X)
    (hcm : ∀ u ∈ Ls, (committedCopy s u).isSome)
    (hex : ∀ u, executedB s u = true ↔ u ∈ X ∨ u ∈ Ls.take j)
    (hl : LeaderOk s)
    (hsort : Ls.Pairwise (fun a b => keyLt (keyS s a) (keyS s b)))
    (hn : Ls[j]? = some n) : execGuard s n := by
  have hdisj : ∀ u ∈ Ls, u ∉ X := hL.2.2.1
  have hmem : ∀ u, u ∈ (executedList s).filter (fun w => w ∉ Ls) ↔ u ∈ X := by
    intro u
    simp only [executedList, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨-, he⟩, hnL⟩
      rcases (hex u).1 he with h | h
      · exact h
      · exact absurd (List.mem_of_mem_take h) hnL
    · intro hx
      have he : executedB s u = true := (hex u).2 (.inl hx)
      exact ⟨⟨mem_boxList (committedCopy_box (executedB_isSome he)), he⟩,
        fun hu => hdisj u hu hx⟩
  refine ⟨Ls, List.mem_of_getElem? hn, hcm, sccStep_congr hmem hL, XClosed_congr hmem hXc, ?_⟩
  intro u hu
  rw [keyAt_eq hl, keyAt_eq hl, ← mem_take_iff_keyLt hsort hn hu, hex u]
  exact ⟨fun h => h.resolve_left (hdisj u hu), .inr⟩

/-! ## The execution step's result -/

/-- The value-tag an execution of copy `c` (first command `c0`) computes (`stepExec`). -/
def execVT0 (s : RState) (c : Copy) : ValTag :=
  match s.prevValTag with
  | none => c.base
  | some pvt => if c.base.t.gt pvt.t then c.base else pvt

/-- The CAS. -/
def execVT1 (vt0 : ValTag) (c0 : Cmd) : ValTag :=
  if c0.oldV = vt0.v then { vt0 with v := c0.v } else vt0

def execVT (s : RState) (c : Copy) (c0 : Cmd) : ValTag :=
  let vt1 : ValTag := execVT1 (execVT0 s c) c0
  { vt1 with t := { vt1.t with rmwc := vt1.t.rmwc + 1 } }

/-- The state and outputs of an execution of copy `c` at `(q, i)`. -/
def execRes (s : RState) (q i : w32) (c : Copy) : Option (RState × List Out) :=
  match c.cmds with
  | [] => some (s.setInst q i { c with status := St.EXECUTED }, [])
  | c0 :: _ =>
    let vt := execVT s c c0
    (sendTo s.id (.executeOverwrite ⟨vt.v, vt.t, c.leader, c.slot⟩)).map fun o =>
      (({ s with prevValTag := some vt } : RState).setInst q i { c with status := St.EXECUTED },
        [o])

theorem stepExec_ok {s s' : RState} {q i : w32} {outs : List Out}
    (h : stepExec s q i = .ok (s', outs)) :
    ∃ c, s.inst q i = some c ∧ execRes s q i c = some (s', outs) := by
  unfold stepExec at h
  cases hc : s.inst q i with
  | none =>
    simp only [hc] at h
    split at h <;> simp [disabled, FailM.failDisabled, bind, Except.bind] at h
  | some c =>
    refine ⟨c, rfl, ?_⟩
    simp only [hc] at h
    unfold execRes execVT
    split at h
    · simp [disabled, FailM.failDisabled, bind, Except.bind] at h
    split at h
    · simp [disabled, FailM.failDisabled, bind, Except.bind] at h
    split at h
    · simp [disabled, FailM.failDisabled, bind, Except.bind] at h
    rcases hcm : c.cmds with _ | ⟨c0, cs⟩
    · simp only [hcm, pure, Except.pure, Except.ok.injEq] at h ⊢; rw [← h]
    · simp only [hcm] at h ⊢
      split at h
      all_goals first
        | (simp [dead, FailM.failDead] at h; done)
        | (rename_i o ho
           rw [Option.map_eq_some_iff]
           refine ⟨o, ho, ?_⟩
           cases h; rfl)
        | (simp [dead, FailM.failDead, bind, Except.bind] at h; done)

/-- The state an execution produces: the copy at `(q, i)` executed, `PrevValTag` maybe
updated, nothing else. -/
theorem execRes_state {s s' : RState} {q i : w32} {c : Copy} {outs : List Out}
    (h : execRes s q i c = some (s', outs)) :
    ∃ pv, s' = ({ s with prevValTag := pv } : RState).setInst q i
      { c with status := St.EXECUTED } := by
  unfold execRes at h
  split at h
  · cases h; exact ⟨s.prevValTag, rfl⟩
  · rename_i c0 _ _
    rw [Option.map_eq_some_iff] at h
    obtain ⟨o, -, ho⟩ := h
    cases ho; exact ⟨_, rfl⟩

theorem committedCopy_setInst_ne {s : RState} {q i : w32} {c : Copy} {n : Node}
    (hn : ¬ (BitVec.ofInt 32 n.1 = q ∧ BitVec.ofInt 32 n.2 = i)) :
    committedCopy (s.setInst q i c) n = committedCopy s n := by
  unfold committedCopy RState.setInst
  simp only [hn, if_false]

theorem committedCopy_pv {s : RState} {pv : Option ValTag} {n : Node} :
    committedCopy ({ s with prevValTag := pv } : RState) n = committedCopy s n := rfl

/-- An execution keeps the committed copies (the executed one becomes EXECUTED). -/
theorem execRes_stable {s s' : RState} {q i : w32} {c : Copy} {outs : List Out}
    (hc : s.inst q i = some c) (h : execRes s q i c = some (s', outs)) : Stable s s' := by
  obtain ⟨pv, rfl⟩ := execRes_state h
  intro n c1 hc1
  by_cases hn : BitVec.ofInt 32 n.1 = q ∧ BitVec.ofInt 32 n.2 = i
  · obtain ⟨h1, h2⟩ := hn
    have := (committedCopy_inst hc1).1
    rw [h1, h2, hc] at this; cases this
    refine ⟨{ c with status := St.EXECUTED }, ?_, rfl, rfl, rfl, rfl⟩
    have hb := committedCopy_box (show (committedCopy s n).isSome by rw [hc1]; rfl)
    unfold committedCopy RState.setInst
    obtain ⟨b0, b1, b2, b3⟩ := hb
    rw [if_pos ⟨b0, b1, b2, by unfold SLOTS; omega⟩]
    simp only [h1, h2, and_self, if_true, or_true]
  · rw [committedCopy_setInst_ne hn, committedCopy_pv]
    exact ⟨c1, hc1, rfl, rfl, rfl, rfl⟩

/-- After an execution, the same instances are committed or executed (the executed one was
committed). -/
theorem execRes_committed_iff {s s' : RState} {q i : w32} {c : Copy} {outs : List Out}
    (hc : s.inst q i = some c) (hs : c.status = St.COMMITTED)
    (h : execRes s q i c = some (s', outs)) (n : Node) :
    (committedCopy s' n).isSome = (committedCopy s n).isSome := by
  obtain ⟨pv, rfl⟩ := execRes_state h
  by_cases hn : BitVec.ofInt 32 n.1 = q ∧ BitVec.ofInt 32 n.2 = i
  · obtain ⟨h1, h2⟩ := hn
    unfold committedCopy RState.setInst
    simp only [h1, h2, and_self, if_true, hc, hs, true_or, or_true]
    split <;> rfl
  · rw [committedCopy_setInst_ne hn, committedCopy_pv]

theorem sendTo_rid (k : Fin 3) (m : Msg) : sendTo (replica2.rid32 k) m = some (.send k m) := by
  unfold sendTo dstOf replica2.rid32
  have hk := k.isLt
  have h1 : sint.Z (W32 (k.val : Int)) = k.val := by
    simp only [sint.Z]; rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)
  rw [dif_pos (by rw [h1]; omega)]
  simp only [Option.map_some, Option.some.injEq]
  congr 1; apply Fin.ext; simp only [h1]; omega

end Perennial.gryff.X
