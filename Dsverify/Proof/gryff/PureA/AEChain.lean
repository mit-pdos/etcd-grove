/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/AEChain.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AE, internal: **the execution chain** (`exec_agree`), from agreement and interference given
as hypotheses (`AgreeH`, `InterfH`; `Pure/Agree.lean` discharges them with `agree_run` and `interf`).

The argument (`notes/unit-AE.md`):
* one global graph `E` over instances: `u → w` iff `u` is committed somewhere in the run (a copy at
  some cut) and `w` is in its deps' range (`AgreeH`: all committed copies of `u` carry one value,
  `gcp u`); the key `kG u = (seq, row, slot)`.
* the order `prec x y`: `y` reaches `x`, and either `x` does not reach `y` (different components) or
  `x`'s key is smaller (one component).
* each replica's executed sequence (instances with a command) is sorted by `prec` and downward
  closed in it among executed instances (`execGuard`: the component `L` of the executed instance
  is closed up to the executed instances, which are dependency-closed; inside `L` the executed
  members are those of smaller key); `prec` is total on executed instances with commands
  (`InterfH`); so any two replicas' sequences are prefix-comparable (`sorted_closed_prefix`);
* the results are a function of the instances' order (`chainR`, the replica's `prevValTag` is its
  last result).
-/
module

public import Dsverify.Proof.gryff.PureA.AEList

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AE

open Perennial Perennial.gryff.model Perennial.gryff.pure kahn
open Perennial.gryff.replica (Node sccStep keyLt XClosed Reach boxList mem_boxList)

/-! ## Coordinates -/

def toN (x : w32 × w32) : Node := (sint.Z x.1, sint.Z x.2)

theorem toN_inj {x y : w32 × w32} (h : toN x = toN y) : x = y := by
  obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
  simp only [toN, Prod.mk.injEq] at h
  exact Prod.ext (BitVec.eq_of_toInt_eq h.1) (BitVec.eq_of_toInt_eq h.2)

theorem z_ofInt {z : Int} (h0 : 0 ≤ z) (h1 : z < SLOTS) : sint.Z (BitVec.ofInt 32 z) = z :=
  BitVec.toInt_ofInt_eq_self (by decide) (by unfold SLOTS at h1; omega)
    (by unfold SLOTS at h1; omega)

theorem cc_of_inst {s : RState} {q i : w32} {c : Copy} (hb : inBox q i = true)
    (hc : s.inst q i = some c) (hs : c.status = St.COMMITTED ∨ c.status = St.EXECUTED) :
    committedCopy s (toN (q, i)) = some c := by
  simp only [inBox, decide_eq_true_eq] at hb
  unfold committedCopy toN
  rw [if_pos hb]
  have e1 : BitVec.ofInt 32 (sint.Z q) = q := BitVec.ofInt_toInt
  have e2 : BitVec.ofInt 32 (sint.Z i) = i := BitVec.ofInt_toInt
  simp only [e1, e2, hc, hs, if_true]

theorem inst_of_cc {s : RState} {n : Node} {c : Copy} (h : committedCopy s n = some c) :
    (0 ≤ n.1 ∧ n.1 < 3 ∧ 0 ≤ n.2 ∧ n.2 < SLOTS) ∧
    inBox (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = true ∧
    toN (BitVec.ofInt 32 n.1, BitVec.ofInt 32 n.2) = n ∧
    s.inst (BitVec.ofInt 32 n.1) (BitVec.ofInt 32 n.2) = some c ∧
    (c.status = St.COMMITTED ∨ c.status = St.EXECUTED) := by
  unfold committedCopy at h
  split at h
  · rename_i hb
    have e1 := z_ofInt hb.1 (by unfold SLOTS; omega)
    have e2 := z_ofInt hb.2.2.1 hb.2.2.2
    have hn : toN (BitVec.ofInt 32 n.1, BitVec.ofInt 32 n.2) = n := by
      simp only [toN, e1, e2]
    refine ⟨hb, ?_, hn, ?_⟩
    · simp only [inBox, decide_eq_true_eq, e1, e2]; exact hb
    · split at h
      · rename_i c' hc'
        split at h
        · cases h; exact ⟨hc', ‹_›⟩
        · cases h
      · cases h
  · cases h

theorem executedB_iff {s : RState} {n : Node} :
    executedB s n = true ↔ ∃ c, committedCopy s n = some c ∧ c.status = St.EXECUTED := by
  unfold executedB
  cases committedCopy s n with
  | none => simp
  | some c => simp

theorem executedB_of_inst {s : RState} {q i : w32} {c : Copy} (hb : inBox q i = true)
    (hc : s.inst q i = some c) (hs : c.status = St.EXECUTED) :
    executedB s (toN (q, i)) = true :=
  executedB_iff.2 ⟨c, cc_of_inst hb hc (Or.inr hs), hs⟩

theorem mem_executedList {s : RState} {n : Node} :
    n ∈ executedList s ↔ executedB s n = true := by
  unfold executedList
  rw [List.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨c, hc, -⟩ := executedB_iff.1 h
  obtain ⟨hb, -⟩ := inst_of_cc hc
  exact mem_boxList ⟨hb.1, hb.2.1, hb.2.2.1, by have := hb.2.2.2; unfold SLOTS at this; omega⟩

/-- `x`'s copy `c` depends on `y` (committed somewhere), in the model's words. -/
theorem depR_of_le {s s' : RState} {x y : Node} {c c' : Copy} (hc : committedCopy s x = some c)
    (hc' : committedCopy s' y = some c')
    (hle : sint.Z (BitVec.ofInt 32 y.2) ≤ sint.Z (c.deps.at (BitVec.ofInt 32 y.1).toNat)) :
    depR s x y := by
  obtain ⟨hb, -⟩ := inst_of_cc hc'
  have e1 := z_ofInt hb.1 (by unfold SLOTS; omega)
  have e2 := z_ofInt hb.2.2.1 hb.2.2.2
  have e3 : (BitVec.ofInt 32 y.1).toNat = y.1.toNat := by
    have := BitVec.toInt_eq_toNat_cond (BitVec.ofInt 32 y.1)
    simp only [sint.Z] at e1
    rw [e1] at this
    split at this <;> omega
  refine ⟨c, hc, hb.1, hb.2.1, hb.2.2.1, ?_⟩
  rw [e2, e3] at hle; exact hle

/-- Global runs are deterministic. -/
theorem gstep_det {c c1 c2 : Cfg gNet} {i : Fin 3} {e : Ev} {x1 x2 : List Ext}
    (h1 : GStep c i e c1 x1) (h2 : GStep c i e c2 x2) : c1 = c2 := by
  obtain ⟨s1, o1, hs1, -, -, hst1, hin1⟩ := h1
  obtain ⟨s2, o2, hs2, -, -, hst2, hin2⟩ := h2
  rw [hs1] at hs2; cases hs2
  cases c1; cases c2
  simp only at hst1 hin1 hst2 hin2
  subst hst1 hin1 hst2 hin2; rfl

theorem grun_det {c c1 c2 : Cfg gNet} {l : List Label} (h1 : GRun c l c1) (h2 : GRun c l c2) :
    c1 = c2 := by
  induction h1 with
  | nil => cases h2; rfl
  | cons s1 _ ih =>
    cases h2 with
    | cons s2 r2 =>
      have := gstep_det s1 s2; subst this; exact ih r2

/-! ## The global graph of a run -/

section glob

variable (l : List Label)

/-- `cp` is a committed copy of `x` at some cut of the run. -/
def CutCom (x : Node) (cp : Copy) : Prop := ∃ k a, committedCopy (cutSt l k a) x = some cp

/-- Agreement: committed copies at any cuts carry one value. -/
def AgreeH : Prop := ∀ x cp cp', CutCom l x cp → CutCom l x cp' →
  cp.cmds = cp'.cmds ∧ cp.seq = cp'.seq ∧ cp.deps = cp'.deps ∧ cp.base = cp'.base

/-- Interference at the end of the run, for instances committed with commands. -/
def InterfH : Prop := ∀ (a a' : Fin 3) x y cp cp',
  committedCopy (cutSt l l.length a) x = some cp → committedCopy (cutSt l l.length a') y = some cp' →
  cp.cmds ≠ [] → cp'.cmds ≠ [] → x ≠ y →
  depR (cutSt l l.length a) x y ∨ depR (cutSt l l.length a') y x

open Classical in
/-- The committed value of `x` (any committed copy). -/
noncomputable def gcp (x : Node) : Copy := if h : ∃ cp, CutCom l x cp then h.choose else default

def Com (x : Node) : Prop := ∃ cp, CutCom l x cp

/-- The global dependency graph. -/
def E (u w : Node) : Prop :=
  Com l u ∧ 0 ≤ w.1 ∧ w.1 < 3 ∧ 0 ≤ w.2 ∧ w.2 ≤ sint.Z ((gcp l u).deps.at w.1.toNat)

/-- The global sort key. -/
noncomputable def kG (u : Node) : Int × Int × Int := (sint.Z (gcp l u).seq, u.1, u.2)

/-- The execution order. -/
def prec (x y : Node) : Prop := Reach (E l) y x ∧ (¬ Reach (E l) x y ∨ keyLt (kG l x) (kG l y))

variable {l}

theorem gcp_spec (hA : AgreeH l) {x : Node} {cp : Copy} (h : CutCom l x cp) :
    (gcp l x).cmds = cp.cmds ∧ (gcp l x).seq = cp.seq ∧ (gcp l x).deps = cp.deps ∧
      (gcp l x).base = cp.base := by
  have h' : ∃ cp, CutCom l x cp := ⟨cp, h⟩
  unfold gcp; rw [dif_pos h']
  exact hA _ _ _ h'.choose_spec h

theorem depR_E (hA : AgreeH l) {k : Nat} {a : Fin 3} {u w : Node} (h : depR (cutSt l k a) u w) :
    E l u w := by
  obtain ⟨c, hc, h1, h2, h3, h4⟩ := h
  have hcc : CutCom l u c := ⟨k, a, hc⟩
  refine ⟨⟨c, hcc⟩, h1, h2, h3, ?_⟩
  rw [(gcp_spec hA hcc).2.2.1]; exact h4

theorem E_depR (hA : AgreeH l) {k : Nat} {a : Fin 3} {u w : Node} {c : Copy}
    (hc : committedCopy (cutSt l k a) u = some c) (h : E l u w) : depR (cutSt l k a) u w := by
  refine ⟨c, hc, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  rw [← (gcp_spec hA ⟨k, a, hc⟩).2.2.1]; exact h.2.2.2.2

theorem reach_E (hA : AgreeH l) {k : Nat} {a : Fin 3} {u w : Node}
    (h : Reach (depR (cutSt l k a)) u w) : Reach (E l) u w := by
  induction h with
  | refl => exact .refl _
  | step a' b c' hab _ ih => exact .step a' b c' (depR_E hA hab) ih

theorem keyAt_eq (hA : AgreeH l) {k : Nat} {a : Fin 3} {u : Node} {c : Copy}
    (hI : Ids (cutSt l k a)) (hc : committedCopy (cutSt l k a) u = some c) :
    keyAt (cutSt l k a) u = kG l u := by
  obtain ⟨hb, -, -, hi, -⟩ := inst_of_cc hc
  obtain ⟨e1, e2⟩ := hI _ _ _ hi
  unfold keyAt kG; rw [hc]
  simp only [e1, e2, (gcp_spec hA ⟨k, a, hc⟩).2.1, z_ofInt hb.1 (by unfold SLOTS; omega),
    z_ofInt hb.2.2.1 hb.2.2.2]

theorem keyLt_irrefl (x : Int × Int × Int) : ¬ keyLt x x := by unfold keyLt; omega
theorem keyLt_trans {x y z : Int × Int × Int} (h1 : keyLt x y) (h2 : keyLt y z) : keyLt x z := by
  unfold keyLt at *; omega

theorem prec_irrefl (x : Node) : ¬ prec l x x := by
  rintro ⟨-, h | h⟩
  · exact h (.refl _)
  · exact keyLt_irrefl _ h

theorem prec_trans {x y z : Node} (h1 : prec l x y) (h2 : prec l y z) : prec l x z := by
  obtain ⟨r1, k1⟩ := h1
  obtain ⟨r2, k2⟩ := h2
  refine ⟨r2.trans r1, ?_⟩
  by_cases hxz : Reach (E l) x z
  · right
    have hxy : Reach (E l) x y := hxz.trans r2
    have hyz : Reach (E l) y z := r1.trans hxz
    exact keyLt_trans (k1.resolve_left (fun hn => hn hxy)) (k2.resolve_left (fun hn => hn hyz))
  · exact Or.inl hxz

/-- Two instances one of which depends on the other are ordered. -/
theorem prec_total {x y : Node} (hne : x ≠ y) (h : E l x y ∨ E l y x) : prec l x y ∨ prec l y x := by
  have kne : kG l x ≠ kG l y := by
    intro e; apply hne; unfold kG at e; simp only [Prod.mk.injEq] at e
    exact Prod.ext e.2.1 e.2.2
  have ktot : keyLt (kG l x) (kG l y) ∨ keyLt (kG l y) (kG l x) := by
    revert kne; unfold keyLt
    obtain ⟨a, b, c⟩ := kG l x; obtain ⟨d, e, f⟩ := kG l y
    simp only [ne_eq, Prod.mk.injEq]; omega
  rcases h with h | h
  · have rxy : Reach (E l) x y := Reach.single h
    by_cases ryx : Reach (E l) y x
    · rcases ktot with k | k
      · exact Or.inl ⟨ryx, Or.inr k⟩
      · exact Or.inr ⟨rxy, Or.inr k⟩
    · exact Or.inr ⟨rxy, Or.inl ryx⟩
  · have ryx : Reach (E l) y x := Reach.single h
    by_cases rxy : Reach (E l) x y
    · rcases ktot with k | k
      · exact Or.inl ⟨ryx, Or.inr k⟩
      · exact Or.inr ⟨rxy, Or.inr k⟩
    · exact Or.inl ⟨ryx, Or.inl rxy⟩

end glob

/-! ## One replica's run -/

section rep

variable {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r : Fin 3)

/-- The result function of the chain. -/
noncomputable def F (l : List Label) (p : Option ValTag) (x : w32 × w32) : ValTag :=
  match (gcp l (toN x)).cmds with
  | c0 :: _ => resNext p (gcp l (toN x)).base c0
  | [] => default

theorem st_cut {j : Nat} (hj : j ≤ (projR l r).length) :
    ∃ k, stOf r ((projR l r).take j) = cutSt l k r := by
  rcases Nat.lt_or_ge j (projR l r).length with hlt | hge
  · obtain ⟨n, -, hn⟩ := proj_index l r (List.getElem?_eq_getElem hlt)
    exact ⟨n, by unfold cutSt; rw [hn]⟩
  · refine ⟨l.length, ?_⟩
    have : j = (projR l r).length := by omega
    subst this
    unfold cutSt; rw [List.take_length, List.take_length]

include h in
theorem hrun : ∃ o, runP gNet r (projR l r) = some (c.st r, o) := grun_state h r

include h in
theorem rstep {j : Nat} {e : Ev} (hj : (projR l r)[j]? = some e) :
    stepR r (stOf r ((projR l r).take j)) e =
      .ok (stOf r ((projR l r).take (j + 1)), outsOf r (projR l r) j) := by
  obtain ⟨o, ho⟩ := hrun h r
  obtain ⟨o', hs⟩ := runP_step ho hj
  have : outsOf r (projR l r) j = o' := by
    unfold outsOf resOf; simp only [hj, hs]
  rw [this]; exact hs

include h in
theorem rkeep {j k : Nat} (hjk : j ≤ k) (hk : k ≤ (projR l r).length) :
    ExecKeep (stOf r ((projR l r).take j)) (stOf r ((projR l r).take k)) := by
  obtain ⟨o, ho⟩ := hrun h r
  exact runP_keep ho hjk hk

/-- The replica's invariant along its events. -/
structure RInv (l : List Label) (r : Fin 3) (j : Nat) : Prop where
  ids : Ids (stOf r ((projR l r).take j))
  pvt : (stOf r ((projR l r).take j)).prevValTag =
    (execSeqA r ((projR l r).take j)).getLast?.map Prod.snd
  exd : ∀ q i cp, (stOf r ((projR l r).take j)).inst q i = some cp → cp.status = St.EXECUTED →
    ∃ j' < j, (projR l r)[j']? = some (.exec q i)
  chain : execSeqA r ((projR l r).take j) =
    chainR (F l) none ((execSeqA r ((projR l r).take j)).map Prod.fst)

theorem rinv_zero : RInv l r 0 := by
  have e : stOf r ((projR l r).take 0) = RState.init r.val := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e]; intro q i cp hc; cases hc
  · rw [e]; rfl
  · rw [e]; intro q i cp hc; cases hc
  · rfl

include h in
theorem rinv_succ (hA : AgreeH l) {j : Nat} (hj : j < (projR l r).length) (I : RInv l r j) :
    RInv l r (j + 1) := by
  obtain ⟨e, he⟩ : ∃ e, (projR l r)[j]? = some e := ⟨_, List.getElem?_eq_getElem hj⟩
  have hstep := rstep h r he
  have hsucc := execSeqA_succ r (projR l r) hj
  by_cases hx : ∃ q i, e = .exec q i
  · obtain ⟨q, i, rfl⟩ := hx
    obtain ⟨cp, hb, hc, hst, -, hinst, hcases⟩ := stepExec_shape hstep
    obtain ⟨k, hk⟩ := st_cut (l := l) r (j := j) (by omega)
    have hcc : committedCopy (stOf r ((projR l r).take j)) (toN (q, i)) = some cp :=
      cc_of_inst hb hc (Or.inl hst)
    have hg' := gcp_spec hA ⟨k, r, hk ▸ hcc⟩
    have hent : entryA r (projR l r) j =
        (execRes (outsOf r (projR l r) j)).map fun vt => ((q, i), vt) := by
      unfold entryA; rw [he]
    have ids' : Ids (stOf r ((projR l r).take (j + 1))) := by
      intro q' i' cp' h'
      rw [hinst, setInst_inst] at h'
      split at h'
      · rename_i hh; obtain ⟨rfl, rfl⟩ := hh; cases h'; exact I.ids _ _ cp hc
      · exact I.ids _ _ _ h'
    have exd' : ∀ q' i' cp', (stOf r ((projR l r).take (j + 1))).inst q' i' = some cp' →
        cp'.status = St.EXECUTED → ∃ j' < j + 1, (projR l r)[j']? = some (.exec q' i') := by
      intro q' i' cp' h' hx'
      rw [hinst, setInst_inst] at h'
      split at h'
      · rename_i hh; obtain ⟨rfl, rfl⟩ := hh; exact ⟨j, by omega, he⟩
      · obtain ⟨j', hj', e'⟩ := I.exd _ _ _ h' hx'; exact ⟨j', by omega, e'⟩
    rcases hcases with ⟨-, hres, hpvt⟩ | ⟨c0, rest, hcons, hres, hpvt⟩
    · have h0 : entryA r (projR l r) j = none := by rw [hent, hres]; rfl
      rw [h0] at hsucc; simp only [Option.toList, List.append_nil] at hsucc
      exact ⟨ids', by rw [hpvt, hsucc, I.pvt], exd', by rw [hsucc]; exact I.chain⟩
    · have h1 : entryA r (projR l r) j = some ((q, i),
          resNext (stOf r ((projR l r).take j)).prevValTag cp.base c0) := by rw [hent, hres]; rfl
      rw [h1] at hsucc; simp only [Option.toList] at hsucc
      refine ⟨ids', ?_, exd', ?_⟩
      · rw [hpvt, hsucc]; simp
      · rw [hsucc, List.map_append]
        simp only [List.map_cons, List.map_nil]
        rw [chainR_snoc, ← I.chain, ← I.pvt]
        simp only [Option.or_none]
        congr 3
        unfold F
        rw [hg'.1, hcons, hg'.2.2.2]
  · have hne : ∀ q i, e ≠ .exec q i := fun q i e' => hx ⟨q, i, e'⟩
    have hI := step_istep hstep hne
    have h0 : entryA r (projR l r) j = none := by
      unfold entryA; rw [he]
      split
      · rename_i q i heq; exact absurd (Option.some.inj heq) (hne q i)
      · rfl
    rw [h0] at hsucc; simp only [Option.toList, List.append_nil] at hsucc
    refine ⟨hI.1 I.ids, by rw [hI.2.1, hsucc, I.pvt], ?_, by rw [hsucc]; exact I.chain⟩
    intro q i cp hc hx'
    obtain ⟨cp0, h0, hx0⟩ := hI.2.2 q i cp hc hx'
    obtain ⟨j', hj', e'⟩ := I.exd q i cp0 h0 hx0
    exact ⟨j', by omega, e'⟩

include h in
theorem rinv_all (hA : AgreeH l) : ∀ j, j ≤ (projR l r).length → RInv l r j
  | 0, _ => rinv_zero r
  | j + 1, hj => rinv_succ h r hA (by omega) (rinv_all hA j (by omega))

theorem st_fin : stOf r ((projR l r).take (projR l r).length) = cutSt l l.length r := by
  unfold cutSt; rw [List.take_length, List.take_length]

theorem entryA_some {es : List Ev} {j : Nat} {x : w32 × w32} {vt : ValTag}
    (he : entryA r es j = some (x, vt)) : es[j]? = some (.exec x.1 x.2) := by
  unfold entryA at he
  split at he
  · rename_i q i heq
    obtain ⟨vt', -, e⟩ := Option.map_eq_some_iff.1 he
    cases e; exact heq
  · cases he

include h in
/-- An executed instance stays executed. -/
theorem ex_after {j k : Nat} {q i : w32} (he : (projR l r)[j]? = some (.exec q i)) (hjk : j < k)
    (hk : k ≤ (projR l r).length) :
    executedB (stOf r ((projR l r).take k)) (toN (q, i)) = true := by
  obtain ⟨cp, hb, -, -, -, hinst, -⟩ := stepExec_shape (rstep h r he)
  have h1 : (stOf r ((projR l r).take (j + 1))).inst q i = some { cp with status := St.EXECUTED } := by
    rw [hinst, setInst_inst, if_pos ⟨rfl, rfl⟩]
  obtain ⟨cp', h2, h3⟩ := rkeep h r (j := j + 1) (k := k) (by omega) hk q i _ h1 rfl
  exact executedB_of_inst hb h2 h3

include h in
/-- An executed instance was executed by an earlier event. -/
theorem ex_before (hA : AgreeH l) {k : Nat} (hk : k ≤ (projR l r).length) {n : Node}
    (hx : executedB (stOf r ((projR l r).take k)) n = true) :
    ∃ j < k, ∃ q i, (projR l r)[j]? = some (.exec q i) ∧ toN (q, i) = n := by
  obtain ⟨cp, hc, hst⟩ := executedB_iff.1 hx
  obtain ⟨-, -, hn, hi, -⟩ := inst_of_cc hc
  obtain ⟨j, hj, e⟩ := (rinv_all h r hA k hk).exd _ _ _ hi hst
  exact ⟨j, hj, _, _, e, hn⟩

include h in
/-- An execution has an entry iff the instance's committed value has a command. -/
theorem entry_iff (hA : AgreeH l) {j : Nat} {q i : w32} (he : (projR l r)[j]? = some (.exec q i)) :
    (∃ vt, entryA r (projR l r) j = some ((q, i), vt)) ↔ (gcp l (toN (q, i))).cmds ≠ [] := by
  have hj : j < (projR l r).length := (List.getElem?_eq_some_iff.1 he).1
  obtain ⟨cp, hb, hc, hst, -, -, hcases⟩ := stepExec_shape (rstep h r he)
  obtain ⟨k, hk⟩ := st_cut (l := l) r (j := j) (by omega)
  have hcc := cc_of_inst hb hc (Or.inl hst)
  have hg' := gcp_spec hA ⟨k, r, hk ▸ hcc⟩
  have hent : entryA r (projR l r) j =
      (execRes (outsOf r (projR l r) j)).map fun vt => ((q, i), vt) := by
    unfold entryA; rw [he]
  rw [hg'.1, hent]
  rcases hcases with ⟨hnil, hres, -⟩ | ⟨c0, rest, hcons, hres, -⟩
  · rw [hres, hnil]; simp
  · rw [hres, hcons]; simp

/-- Replica `r`'s executed instances (with commands). -/
noncomputable def Lr (l : List Label) (r : Fin 3) : List (w32 × w32) :=
  (execSeqA r (projR l r)).map Prod.fst

include h in
theorem mem_Lr (hA : AgreeH l) {x : w32 × w32} :
    x ∈ Lr l r ↔ ∃ j : Nat, (projR l r)[j]? = some (Ev.exec x.1 x.2) ∧ (gcp l (toN x)).cmds ≠ [] := by
  unfold Lr execSeqA
  simp only [List.mem_map, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨⟨x', vt⟩, ⟨j, -, hj⟩, rfl⟩
    have he := entryA_some r hj
    exact ⟨j, he, (entry_iff h r hA he).1 ⟨vt, hj⟩⟩
  · rintro ⟨j, he, hc⟩
    obtain ⟨vt, hvt⟩ := (entry_iff h r hA he).2 hc
    exact ⟨((x.1, x.2), vt), ⟨j, (List.getElem?_eq_some_iff.1 he).1, hvt⟩, rfl⟩

end rep

section all

variable {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c)

/-- Executed somewhere, with a command. -/
def DW (l : List Label) (x : w32 × w32) : Prop := ∃ a, x ∈ Lr l a

include h in
theorem DW_fin (hA : AgreeH l) {x : w32 × w32} (hx : DW l x) :
    (gcp l (toN x)).cmds ≠ [] ∧
      ∃ a cp, committedCopy (cutSt l l.length a) (toN x) = some cp ∧ cp.cmds ≠ [] := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨j, he, hcm⟩ := (mem_Lr h a hA).1 ha
  have hj : j < (projR l a).length := (List.getElem?_eq_some_iff.1 he).1
  have hex := ex_after h a he hj (Nat.le_refl _)
  rw [st_fin] at hex
  obtain ⟨cp, hc, -⟩ := executedB_iff.1 hex
  refine ⟨hcm, a, cp, hc, ?_⟩
  rw [← (gcp_spec hA ⟨_, a, hc⟩).1]; exact hcm

include h in
theorem DW_E (hA : AgreeH l) (hI : InterfH l) {x y : w32 × w32} (hx : DW l x) (hy : DW l y)
    (hne : x ≠ y) : E l (toN x) (toN y) ∨ E l (toN y) (toN x) := by
  obtain ⟨-, a, cp, hc, hcm⟩ := DW_fin h hA hx
  obtain ⟨-, a', cp', hc', hcm'⟩ := DW_fin h hA hy
  rcases hI a a' _ _ cp cp' hc hc' hcm hcm' (fun e => hne (toN_inj e)) with d | d
  · exact Or.inl (depR_E hA d)
  · exact Or.inr (depR_E hA d)

end all

section guard

variable {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r : Fin 3)

include h in
/-- **The guard at an execution**, in terms of the global graph. -/
theorem guard_facts (hA : AgreeH l) {j : Nat} {q i : w32} (he : (projR l r)[j]? = some (.exec q i)) :
    ∃ L : List Node, toN (q, i) ∈ L ∧
      (∀ u ∈ L, ∀ w ∈ L, Reach (E l) u w) ∧
      (∀ u w, Reach (E l) u w → (u ∈ L ∨ executedB (stOf r ((projR l r).take j)) u = true) →
        (w ∈ L ∨ executedB (stOf r ((projR l r).take j)) w = true)) ∧
      (∀ u w, Reach (E l) u w → (executedB (stOf r ((projR l r).take j)) u = true ∧ u ∉ L) →
        (executedB (stOf r ((projR l r).take j)) w = true ∧ w ∉ L)) ∧
      (∀ u ∈ L, executedB (stOf r ((projR l r).take j)) u = true ↔ keyLt (kG l u) (kG l (toN (q, i)))) ∧
      executedB (stOf r ((projR l r).take j)) (toN (q, i)) = false := by
  have hj : j < (projR l r).length := (List.getElem?_eq_some_iff.1 he).1
  have Ids0 := (rinv_all h r hA j (by omega)).ids
  obtain ⟨cp, hb, hc, hst, hg, -, -⟩ := stepExec_shape (rstep h r he)
  have hcc := cc_of_inst hb hc (Or.inl hst)
  obtain ⟨k, hk⟩ := st_cut (l := l) r (j := j) (by omega)
  generalize stOf r ((projR l r).take j) = s at *
  subst hk
  obtain ⟨L, hnL, hcomL, hscc, hXC, hiff⟩ := hg
  change toN (q, i) ∈ L at hnL
  have mX : ∀ w, w ∈ (executedList (cutSt l k r)).filter (fun w => w ∉ L) ↔
      executedB (cutSt l k r) w = true ∧ w ∉ L := by
    intro w; simp [List.mem_filter, mem_executedList]
  have comL : ∀ u ∈ L, ∃ c, committedCopy (cutSt l k r) u = some c := fun u hu =>
    Option.isSome_iff_exists.1 (hcomL u hu)
  have comX : ∀ u, executedB (cutSt l k r) u = true → ∃ c, committedCopy (cutSt l k r) u = some c :=
    fun u hu => by obtain ⟨c, h1, -⟩ := executedB_iff.1 hu; exact ⟨c, h1⟩
  obtain ⟨-, -, -, hcl, hre⟩ := hscc
  -- one step of `E` from `L` or the executed instances
  have stepL : ∀ u w, E l u w → u ∈ L → w ∈ L ∨ (executedB (cutSt l k r) w = true ∧ w ∉ L) := by
    intro u w hE hu
    obtain ⟨c1, h1⟩ := comL u hu
    rcases hcl u hu w (E_depR hA h1 hE) with hw | hw
    · exact Or.inr ((mX w).1 hw)
    · exact Or.inl hw
  have stepX : ∀ u w, E l u w → (executedB (cutSt l k r) u = true ∧ u ∉ L) →
      executedB (cutSt l k r) w = true ∧ w ∉ L := by
    intro u w hE hu
    obtain ⟨c1, h1⟩ := comX u hu.1
    exact (mX w).1 (hXC u ((mX u).2 hu) w (E_depR hA h1 hE))
  refine ⟨L, hnL, fun u hu w hw => reach_E hA (hre u hu w hw), ?_, ?_, ?_, ?_⟩
  · intro u w hr
    induction hr with
    | refl => exact id
    | step a b c' hab _ ih =>
      intro ha
      apply ih
      by_cases haL : a ∈ L
      · rcases stepL a b hab haL with hb' | hb'
        · exact Or.inl hb'
        · exact Or.inr hb'.1
      · rcases ha with ha | ha
        · exact absurd ha haL
        · exact Or.inr (stepX a b hab ⟨ha, haL⟩).1
  · intro u w hr
    induction hr with
    | refl => exact id
    | step a b c' hab _ ih => exact fun ha => ih (stepX a b hab ha)
  · intro u hu
    obtain ⟨c1, h1⟩ := comL u hu
    rw [hiff u hu, keyAt_eq hA Ids0 h1]
    exact Iff.of_eq (congrArg _ (keyAt_eq hA Ids0 hcc))
  · unfold executedB; rw [hcc]; simp only [hst]; decide

include h in
theorem sorted_core (hA : AgreeH l) (hI : InterfH l) {j1 j2 : Nat} {x y : w32 × w32}
    (hlt : j1 < j2) (h1 : (projR l r)[j1]? = some (.exec x.1 x.2))
    (h2 : (projR l r)[j2]? = some (.exec y.1 y.2)) (hx : x ∈ Lr l r) (hy : y ∈ Lr l r) :
    prec l (toN x) (toN y) := by
  have hj2 : j2 < (projR l r).length := (List.getElem?_eq_some_iff.1 h2).1
  obtain ⟨L, hnL, hstr, -, hXC, hiff, hnex⟩ := guard_facts h r hA h2
  have hex : executedB (stOf r ((projR l r).take j2)) (toN x) = true :=
    ex_after h r h1 hlt (by omega)
  have hne : x ≠ y := by
    intro e; subst e; rw [hnex] at hex; cases hex
  by_cases hxL : toN x ∈ L
  · exact ⟨hstr _ hnL _ hxL, Or.inr ((hiff _ hxL).1 hex)⟩
  · rcases DW_E h hA hI ⟨r, hx⟩ ⟨r, hy⟩ hne with d | d
    · have := (hXC _ _ (Reach.single d) ⟨hex, hxL⟩).1
      rw [hnex] at this; cases this
    · refine ⟨Reach.single d, Or.inl fun hr => ?_⟩
      have := (hXC _ _ hr ⟨hex, hxL⟩).1
      rw [hnex] at this; cases this

include h in
theorem closed_core (hA : AgreeH l) {x y : w32 × w32} (hy : y ∈ Lr l r) (hx : DW l x)
    (hp : prec l (toN x) (toN y)) : x ∈ Lr l r := by
  obtain ⟨j, he, -⟩ := (mem_Lr h r hA).1 hy
  have hj : j < (projR l r).length := (List.getElem?_eq_some_iff.1 he).1
  obtain ⟨L, hnL, hstr, hRC, -, hiff, -⟩ := guard_facts h r hA he
  obtain ⟨hr, hk⟩ := hp
  have hex : executedB (stOf r ((projR l r).take j)) (toN x) = true := by
    rcases hRC _ _ hr (Or.inl hnL) with hxL | hxe
    · apply Classical.byContradiction
      intro hn
      have hnk : ¬ keyLt (kG l (toN x)) (kG l (toN (y.1, y.2))) := fun k => hn ((hiff _ hxL).2 k)
      rcases hk with hk | hk
      · exact hk (hstr _ hxL _ hnL)
      · exact hnk hk
    · exact hxe
  obtain ⟨j', -, q', i', he', hn⟩ := ex_before h r hA (by omega) hex
  have e := toN_inj hn
  subst e
  exact (mem_Lr h r hA).2 ⟨j', he', (DW_fin h hA hx).1⟩

include h in
theorem Lr_sorted (hA : AgreeH l) (hI : InterfH l) :
    (Lr l r).Pairwise (fun x y => prec l (toN x) (toN y)) := by
  unfold Lr execSeqA
  rw [List.pairwise_map]
  refine List.Pairwise.filterMap _ ?_ List.pairwise_lt_range
  intro j1 j2 hlt b1 hb1 b2 hb2
  obtain ⟨x, v1⟩ := b1
  obtain ⟨y, v2⟩ := b2
  have e1 := entryA_some r hb1
  have e2 := entryA_some r hb2
  have m : ∀ {j z vt}, entryA r (projR l r) j = some (z, vt) → z ∈ Lr l r := by
    intro j z vt hz
    unfold Lr execSeqA
    exact List.mem_map.2 ⟨(z, vt), List.mem_filterMap.2 ⟨j, List.mem_range.2
      (List.getElem?_eq_some_iff.1 (entryA_some r hz)).1, hz⟩, rfl⟩
  exact sorted_core h r hA hI hlt e1 e2 (m hb1) (m hb2)

end guard

/-- **The chain**: any two replicas' executed sequences are prefix-comparable. -/
theorem chain_agree {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c)
    (hA : AgreeH l) (hI : InterfH l) (r r' : Fin 3) :
    execSeqA r (projR l r) <+: execSeqA r' (projR l r') ∨
      execSeqA r' (projR l r') <+: execSeqA r (projR l r) := by
  have ch : ∀ a : Fin 3, execSeqA a (projR l a) = chainR (F l) none (Lr l a) := by
    intro a
    have := (rinv_all h a hA _ (Nat.le_refl _)).chain
    rw [List.take_length] at this
    exact this
  have hp := sorted_closed_prefix (lt := fun x y => prec l (toN x) (toN y))
    (fun x => prec_irrefl _) (fun _ _ _ h1 h2 => prec_trans h1 h2) (DW l) (Lr l r) (Lr l r')
    (fun x y hx hy hne => prec_total (fun e => hne (toN_inj e)) (DW_E h hA hI hx hy hne))
    (Lr_sorted h r hA hI) (Lr_sorted h r' hA hI) (fun x hx => ⟨r, hx⟩) (fun x hx => ⟨r', hx⟩)
    (fun y hy x hx hp => closed_core h r hA hy hx hp) (fun y hy x hx hp => closed_core h r' hA hy hx hp)
  rw [ch r, ch r']
  rcases hp with hp | hp
  · exact Or.inl (chainR_prefix _ _ _ _ hp)
  · exact Or.inr (chainR_prefix _ _ _ _ hp)

/-- A replica's executed instances are distinct. -/
theorem chain_nodup {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c)
    (hA : AgreeH l) (hI : InterfH l) (r : Fin 3) : (Lr l r).Nodup :=
  (Lr_sorted h r hA hI).imp fun hp e => by subst e; exact prec_irrefl _ hp

/-- **Equal results**: an instance executed (with a command) at two replicas has one result. -/
theorem chain_same {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c)
    (hA : AgreeH l) (hI : InterfH l) (r r' : Fin 3) {x : w32 × w32} {vt vt' : ValTag}
    (hx : (x, vt) ∈ execSeqA r (projR l r)) (hx' : (x, vt') ∈ execSeqA r' (projR l r')) :
    vt = vt' := by
  rcases chain_agree h hA hI r r' with hp | hp
  · exact nodup_fst_eq (chain_nodup h hA hI r') (hp.subset hx) hx'
  · exact nodup_fst_eq (chain_nodup h hA hI r) hx (hp.subset hx')

end Perennial.gryff.pureA.AE
