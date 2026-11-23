/-
`handlePreAcceptReply`: the handler's branches (`par_cases`), the bookkeeping after counting a
reply (`parLb`), `mergeAttributes` (`merge_spec`), and the facts every counting branch shares
(`par_common`: the guards, the Phase 1, the counted replies with the new one).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.LbCount

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace PARProof

open HStepProof HLocal SafeProof AuxProof PrepReplyProof LbCountProof

/-- The bookkeeping after counting reply `m`: `preAcceptOKs + 1`. -/
def parLb1 (lb : LbRec) : LbRec := { lb with preAcceptOKs := lb.preAcceptOKs + 1 }

/-- ... then the reply's ballot, attributes and status if it carries a higher vote. -/
def parLb2 (lb : LbRec) (m : PreAcceptReply) : LbRec :=
  if (parLb1 lb).ballot.slt m.vballot then
    { parLb1 lb with ballot := m.vballot, seq := m.seq, deps := m.deps, status := m.status }
  else parLb1 lb

/-- The merge of the bookkeeping's attributes with the reply's. -/
def parMg (lb : LbRec) (m : PreAcceptReply) : w32 × List w32 × Bool :=
  mergeAttributes (parLb2 lb m).seq (parLb2 lb m).deps m.seq m.deps

/-- ... then `allEqual`. -/
def parLb3 (lb : LbRec) (m : PreAcceptReply) : LbRec :=
  { parLb2 lb m with allEqual := (parLb2 lb m).allEqual && (parMg lb m).2.2 }

/-- The bookkeeping after `handlePreAcceptReply` counted reply `m` (before the fast/slow
decision): the merged attributes while pre-accepting. -/
def parLb (lb : LbRec) (m : PreAcceptReply) : LbRec :=
  if (parLb3 lb m).status.sle stPREACCEPTED_EQ then
    { parLb3 lb m with deps := (parMg lb m).2.1, seq := (parMg lb m).1 }
  else parLb3 lb m

/-- The fast path's precondition (`allEqual` and the initial ballot). -/
def parPre (lb : LbRec) (m : PreAcceptReply) : Bool :=
  (parLb lb m).allEqual && isInitialBallot (parLb2 lb m).lastTriedBallot m.replica

/-- The fast path's condition. -/
def parFast (lb : LbRec) (m : PreAcceptReply) : Bool :=
  (W64 (2 * fR - 1)).sle (parLb lb m).preAcceptOKs && parPre lb m

/-- The slow path's condition. -/
def parSlow (lb : LbRec) (m : PreAcceptReply) : Bool :=
  (W64 (nR / 2)).sle (parLb lb m).preAcceptOKs &&
    Bool.or (!(parPre lb m)) ((parLb lb m).preAcceptsSent.sle (parLb lb m).preAcceptOKs)

/-- The fast path's result. -/
def parFastOut (σ : RState) (w : InstRec) (lb : LbRec) (m : PreAcceptReply) : RState × List Out :=
  let lb := { parLb lb m with status := stCOMMITTED }
  let inst := { w with status := stCOMMITTED, bal := lb.ballot, cmds := lb.cmds,
                       deps := lb.deps, seq := lb.seq, lb := some lb }
  let σ := updateCommitted ((bumpRecvBallot σ m.ballot).setInst (parX m) inst) (parX m).q
  (σ, [Out.ev (.commit (parX m) lb.ballot (lbVal lb)), Out.ev (.fastCommit (parX m) (lbVal lb)),
       Out.bcast (bcastCommitOf σ (parX m) (commitOf σ m.replica m.inst lb))])

/-- The slow path's result. -/
def parSlowOut (σ : RState) (w : InstRec) (lb : LbRec) (m : PreAcceptReply) : RState × List Out :=
  let lb := { parLb lb m with status := stACCEPTED }
  let inst := { w with status := stACCEPTED, bal := lb.ballot, cmds := lb.cmds,
                       deps := lb.deps, seq := lb.seq, lb := some lb }
  let σ := (bumpRecvBallot σ m.ballot).setInst (parX m) inst
  (σ, [Out.ev (.vote (parX m) inst.vbal stACCEPTED (lbVal lb)),
       Out.ev (.accept (parX m) lb.lastTriedBallot (lbVal lb)),
       Out.bcast (bcastAcceptOf σ (parX m) (acceptOf σ m.replica m.inst lb))])

/-- `handlePreAcceptReply` with the counted bookkeeping and the paths named. -/
theorem hPAR_eq (σ : RState) (m : PreAcceptReply) :
    hPreAcceptReply σ m =
      match σ.inst (parX m) with
      | none => (σ, [])
      | some inst =>
        match inst.lb with
        | none => (σ, [])
        | some lb =>
          if stGe inst.status stCOMMITTED then (bumpRecvBallot σ m.ballot, [])
          else if lb.lastTriedBallot.slt inst.bal then (bumpRecvBallot σ m.ballot, [])
          else if m.ballot.slt lb.lastTriedBallot then (bumpRecvBallot σ m.ballot, [])
          else if lb.lastTriedBallot.slt m.ballot then
            nackBranch (bumpRecvBallot σ m.ballot) (parX m) inst lb
          else if ¬ (lb.status = stPREACCEPTED ∨ lb.status = stPREACCEPTED_EQ) then
            (bumpRecvBallot σ m.ballot, [])
          else if parFast lb m then parFastOut σ inst lb m
          else if parSlow lb m then parSlowOut σ inst lb m
          else ((bumpRecvBallot σ m.ballot).setInst (parX m) { inst with lb := some (parLb lb m) },
            []) := by
  rfl

/-- The branches of `handlePreAcceptReply`. -/
theorem par_cases (σ : RState) (m : PreAcceptReply) :
    hPreAcceptReply σ m = (σ, []) ∨ hPreAcceptReply σ m = (bumpRecvBallot σ m.ballot, []) ∨
    (∃ w lb, σ.inst (parX m) = some w ∧ w.lb = some lb ∧
      lb.lastTriedBallot.slt m.ballot = true) ∨
    ∃ w lb, σ.inst (parX m) = some w ∧ w.lb = some lb ∧ stGe w.status stCOMMITTED = false ∧
      lb.lastTriedBallot.slt w.bal = false ∧ m.ballot = lb.lastTriedBallot ∧ isPA lb.status ∧
      ((parFast lb m = true ∧ hPreAcceptReply σ m = parFastOut σ w lb m) ∨
       (parFast lb m = false ∧ parSlow lb m = true ∧ hPreAcceptReply σ m = parSlowOut σ w lb m) ∨
       (parFast lb m = false ∧ parSlow lb m = false ∧
        hPreAcceptReply σ m =
          ((bumpRecvBallot σ m.ballot).setInst (parX m) { w with lb := some (parLb lb m) }, []))) := by
  rw [hPAR_eq]
  cases hw : σ.inst (parX m) with
  | none => exact Or.inl rfl
  | some w =>
    simp only []
    cases hlb : w.lb with
    | none => exact Or.inl rfl
    | some lb =>
      simp only []
      by_cases c1 : stGe w.status stCOMMITTED = true
      · rw [if_pos c1]; exact Or.inr (Or.inl rfl)
      rw [if_neg c1]
      by_cases c2 : lb.lastTriedBallot.slt w.bal = true
      · rw [if_pos c2]; exact Or.inr (Or.inl rfl)
      rw [if_neg c2]
      by_cases c3 : m.ballot.slt lb.lastTriedBallot = true
      · rw [if_pos c3]; exact Or.inr (Or.inl rfl)
      rw [if_neg c3]
      by_cases c4 : lb.lastTriedBallot.slt m.ballot = true
      · exact Or.inr (Or.inr (Or.inl ⟨w, lb, rfl, hlb, c4⟩))
      rw [if_neg c4]
      by_cases c5 : ¬ (lb.status = stPREACCEPTED ∨ lb.status = stPREACCEPTED_EQ)
      · rw [if_pos c5]; exact Or.inr (Or.inl rfl)
      rw [if_neg c5]
      have c5' : isPA lb.status := Classical.not_not.mp c5
      have hbeq : m.ballot = lb.lastTriedBallot := by
        have h1 := (slt_false _ _).mp (by simpa using c3)
        have h2 := (slt_false _ _).mp (by simpa using c4)
        exact zz_inj (by omega)
      refine Or.inr (Or.inr (Or.inr ⟨w, lb, rfl, hlb, by simpa using c1, by simpa using c2, hbeq,
        c5', ?_⟩))
      by_cases cf : parFast lb m = true
      · exact Or.inl ⟨cf, by rw [if_pos cf]⟩
      · have cf' : parFast lb m = false := by simpa using cf
        rw [if_neg cf]
        by_cases cs : parSlow lb m = true
        · exact Or.inr (Or.inl ⟨cf', cs, by rw [if_pos cs]⟩)
        · exact Or.inr (Or.inr ⟨cf', by simpa using cs, by rw [if_neg cs]⟩)

/-! ## `mergeAttributes` -/

/-- The fold step of `mergeAttributes`. -/
def mgStep (d2 : List w32) (acc : List w32 × Bool) (q : Nat) : List w32 × Bool :=
  let a := acc.1.getD q (W32 0)
  let b := d2.getD q (W32 0)
  if a ≠ b then (if a.slt b then acc.1.set q b else acc.1, false) else acc

theorem merge_fst (s1 s2 : w32) (d1 d2 : List w32) :
    (mergeAttributes s1 d1 s2 d2).1 = if s1 ≠ s2 ∧ s1.slt s2 then s2 else s1 := rfl

theorem merge_deps (s1 s2 : w32) (d1 d2 : List w32) :
    (mergeAttributes s1 d1 s2 d2).2.1 = ((List.range nR).foldl (mgStep d2) (d1, true)).1 := by
  simp only [mergeAttributes]; rfl

theorem merge_flag (s1 s2 : w32) (d1 d2 : List w32) :
    (mergeAttributes s1 d1 s2 d2).2.2 =
      ((s1 == s2) && ((List.range nR).foldl (mgStep d2) (d1, true)).2) := by
  unfold mergeAttributes; rfl

/-- The pointwise maximum. -/
def mgMax (a b : w32) : w32 := if a.slt b then b else a

theorem mg_fold (d1 d2 : List w32) (h1 : d1.length = nR) : ∀ k ≤ nR,
    ((List.range k).foldl (mgStep d2) (d1, true)).1.length = nR ∧
    (∀ q, k ≤ q → ((List.range k).foldl (mgStep d2) (d1, true)).1.getD q (W32 0) =
      d1.getD q (W32 0)) ∧
    (∀ q < k, ((List.range k).foldl (mgStep d2) (d1, true)).1.getD q (W32 0) =
      mgMax (d1.getD q (W32 0)) (d2.getD q (W32 0))) ∧
    (((List.range k).foldl (mgStep d2) (d1, true)).2 = true ↔
      ∀ q < k, d1.getD q (W32 0) = d2.getD q (W32 0)) := by
  intro k
  induction k with
  | zero => intro _; simp [h1]
  | succ k ih =>
    intro hk
    obtain ⟨i1, i2, i3, i4⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range k).foldl (mgStep d2) (d1, true) = r at i1 i2 i3 i4
    have ha := i2 k (Nat.le_refl _)
    unfold mgStep
    by_cases hab : r.1.getD k (W32 0) = d2.getD k (W32 0)
    · rw [if_neg (by simpa using hab)]
      refine ⟨i1, fun q hq => i2 q (by omega), fun q hq => ?_, ?_⟩
      · by_cases hqk : q = k
        · subst hqk; rw [ha] at hab ⊢; rw [← hab]; simp [mgMax, BitVec.slt]
        · exact i3 q (by omega)
      · rw [i4]; constructor
        · intro h q hq
          by_cases hqk : q = k
          · subst hqk; rw [← ha]; exact hab
          · exact h q (by omega)
        · intro h q hq; exact h q (by omega)
    · rw [if_pos hab]
      have hne : ¬ ∀ q < k + 1, d1.getD q (W32 0) = d2.getD q (W32 0) :=
        fun h => hab (by rw [ha]; exact h k (by omega))
      refine ⟨?_, fun q hq => ?_, fun q hq => ?_, by simpa using hne⟩
      · split <;> simp [i1]
      · split
        · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
            ← List.getD_eq_getElem?_getD]; exact i2 q (by omega)
        · exact i2 q (by omega)
      · by_cases hqk : q = k
        · subst hqk
          rw [ha] at hab ⊢
          unfold mgMax
          split
          · show (r.1.set q _).getD q _ = _
            rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]; rfl
          · exact ha
        · split
          · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
              ← List.getD_eq_getElem?_getD]; exact i3 q (by omega)
          · exact i3 q (by omega)


theorem getD_ext {d1 d2 : List w32} (h1 : d1.length = nR) (h2 : d2.length = nR)
    (h : ∀ q < nR, d1.getD q (W32 0) = d2.getD q (W32 0)) : d1 = d2 := by
  apply List.ext_getElem (by omega)
  intro q hq1 hq2
  have := h q (by omega)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq1,
    List.getElem?_eq_getElem hq2] using this

theorem getD_mem {d : List w32} {q : Nat} (h : q < d.length) : d.getD q (W32 0) ∈ d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem w32_zero : (0 : w32) = W32 0 := by decide

theorem mgMax_cases (a b : w32) : (mgMax a b = a ∨ mgMax a b = b) ∧ zz a ≤ zz (mgMax a b) ∧
    zz b ≤ zz (mgMax a b) := by
  unfold mgMax
  cases h : a.slt b
  · have := (slt_false a b).mp h; simp; omega
  · have := (slt_iff a b).mp h; simp; omega

theorem merge_res (s1 s2 : w32) (d1 d2 : List w32) (h1 : d1.length = nR) :
    (mergeAttributes s1 d1 s2 d2).2.1.length = nR ∧
    ∀ q < nR, (mergeAttributes s1 d1 s2 d2).2.1.getD q (W32 0) =
      mgMax (d1.getD q (W32 0)) (d2.getD q (W32 0)) := by
  rw [merge_deps]
  obtain ⟨i1, -, i3, -⟩ := mg_fold d1 d2 h1 nR (Nat.le_refl _)
  exact ⟨i1, i3⟩

theorem merge_self (s : w32) (d : List w32) (h : d.length = nR) :
    mergeAttributes s d s d = (s, d, true) := by
  obtain ⟨r1, r2⟩ := merge_res s s d d h
  obtain ⟨-, -, -, i4⟩ := mg_fold d d h nR (Nat.le_refl _)
  have e1 : (mergeAttributes s d s d).1 = s := by rw [merge_fst]; simp
  have e2 : (mergeAttributes s d s d).2.1 = d :=
    getD_ext r1 h (fun q hq => by rw [r2 q hq]; unfold mgMax; simp [BitVec.slt])
  have e3 : (mergeAttributes s d s d).2.2 = true := by
    rw [merge_flag]; simp only [beq_self_eq_true, Bool.true_and]
    exact i4.mpr (fun _ _ => rfl)
  exact Prod.ext e1 (Prod.ext e2 e3)

/-- `mergeAttributes` on attributes with `N` entries: the pointwise maximum (entries from either
side), the larger seq, and `true` exactly when both were equal. -/
theorem merge_spec (s1 s2 : w32) (d1 d2 : List w32) (h1 : d1.length = nR) (h2 : d2.length = nR) :
    depsLe d1 (mergeAttributes s1 d1 s2 d2).2.1 ∧ depsLe d2 (mergeAttributes s1 d1 s2 d2).2.1 ∧
    zz s1 ≤ zz (mergeAttributes s1 d1 s2 d2).1 ∧ zz s2 ≤ zz (mergeAttributes s1 d1 s2 d2).1 ∧
    ((mergeAttributes s1 d1 s2 d2).1 = s1 ∨ (mergeAttributes s1 d1 s2 d2).1 = s2) ∧
    (∀ q < nR, (mergeAttributes s1 d1 s2 d2).2.1.getD q 0 = d1.getD q 0 ∨
      (mergeAttributes s1 d1 s2 d2).2.1.getD q 0 = d2.getD q 0) ∧
    ((mergeAttributes s1 d1 s2 d2).2.2 = true ↔ s1 = s2 ∧ d1 = d2) := by
  obtain ⟨r1, r2⟩ := merge_res s1 s2 d1 d2 h1
  obtain ⟨-, -, -, i4⟩ := mg_fold d1 d2 h1 nR (Nat.le_refl _)
  have r2' := r2
  simp only [← w32_zero] at r2'
  refine ⟨⟨h1, r1, fun q hq => by rw [r2' q hq]; exact (mgMax_cases _ _).2.1⟩,
    ⟨h2, r1, fun q hq => by rw [r2' q hq]; exact (mgMax_cases _ _).2.2⟩, ?_, ?_, ?_,
    fun q hq => by rw [r2' q hq]; exact (mgMax_cases _ _).1, ?_⟩
  · rw [merge_fst]; split
    · rename_i h; have := (slt_iff _ _).mp h.2; omega
    · exact Int.le_refl _
  · rw [merge_fst]; split
    · exact Int.le_refl _
    · rename_i h
      by_cases e : s1 = s2
      · rw [e]; exact Int.le_refl _
      · have := (slt_false s1 s2).mp (by simpa [e] using h); exact this
  · rw [merge_fst]; split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rw [merge_flag, Bool.and_eq_true, i4, beq_iff_eq]
    constructor
    · rintro ⟨e, h⟩; exact ⟨e, getD_ext h1 h2 h⟩
    · rintro ⟨e, rfl⟩; exact ⟨e, fun _ _ => rfl⟩

theorem merge_depsOk (s1 s2 : w32) (d1 d2 : List w32) (h1 : depsOk d1) (h2 : depsOk d2) :
    depsOk (mergeAttributes s1 d1 s2 d2).2.1 := by
  obtain ⟨r1, r2⟩ := merge_res s1 s2 d1 d2 h1.1
  refine ⟨r1, fun d hd => ?_⟩
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hd
  have hq' : q < nR := by rw [r1] at hq; exact hq
  have := h1.1
  have := h2.1
  have e := r2 q hq'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq] at e
  simp only [Option.getD_some] at e
  rw [e]
  rcases (mgMax_cases (d1.getD q (W32 0)) (d2.getD q (W32 0))).1 with h | h <;> rw [h]
  · exact h1.2 _ (getD_mem (by omega))
  · exact h2.2 _ (getD_mem (by have := h2.1; omega))


/-! ## The counted bookkeeping -/

theorem par_w64_succ (o : w64) (h : o.toNat ≤ 5) : (o + 1).toNat = o.toNat + 1 := by
  rw [BitVec.toNat_add]; simp; omega

theorem par_nodup_len_le {Q : List Nat} (hQ : Q.Nodup) (h : ∀ a ∈ Q, a < nR) :
    Q.length ≤ nR := by
  have := (List.subperm_of_subset hQ (fun a ha => List.mem_range.mpr (h a ha)) :
    Q.Subperm (List.range nR)).length_le
  simpa using this

theorem depsLe_refl {d : List w32} (h : d.length = nR) : depsLe d d :=
  ⟨h, h, fun _ _ => Int.le_refl _⟩

theorem depsLe_trans {d1 d2 d3 : List w32} (h1 : depsLe d1 d2) (h2 : depsLe d2 d3) :
    depsLe d1 d3 :=
  ⟨h1.1, h2.2.1, fun q hq => Int.le_trans (h1.2.2 q hq) (h2.2.2 q hq)⟩

theorem pa_sle {st : w8} (h : isPA st) : st.sle stPREACCEPTED_EQ = true := by
  rcases h with rfl | rfl <;> decide

/-- The reply carries a higher vote: the bookkeeping takes it. -/
theorem parLb_upd (lb : LbRec) (p : PreAcceptReply) (hU : lb.ballot.slt p.vballot = true)
    (hd : p.deps.length = nR) :
    parLb lb p = { lb with preAcceptOKs := lb.preAcceptOKs + 1, ballot := p.vballot,
                           seq := p.seq, deps := p.deps, status := p.status } := by
  have e2 : parLb2 lb p = { lb with preAcceptOKs := lb.preAcceptOKs + 1, ballot := p.vballot,
                                    seq := p.seq, deps := p.deps, status := p.status } := by
    unfold parLb2; rw [if_pos (by exact hU)]; rfl
  have em : parMg lb p = (p.seq, p.deps, true) := by
    unfold parMg; rw [e2]; exact merge_self _ _ hd
  unfold parLb parLb3
  rw [em, e2]
  split <;> simp

/-- The reply carries no higher vote: the bookkeeping merges it. -/
theorem parLb_noupd (lb : LbRec) (p : PreAcceptReply) (hU : lb.ballot.slt p.vballot = false)
    (hpa : isPA lb.status) :
    parLb lb p = { lb with preAcceptOKs := lb.preAcceptOKs + 1,
                           allEqual := lb.allEqual && (mergeAttributes lb.seq lb.deps p.seq p.deps).2.2,
                           deps := (mergeAttributes lb.seq lb.deps p.seq p.deps).2.1,
                           seq := (mergeAttributes lb.seq lb.deps p.seq p.deps).1 } := by
  have e2 : parLb2 lb p = { lb with preAcceptOKs := lb.preAcceptOKs + 1 } := by
    unfold parLb2; rw [if_neg (by simpa [parLb1] using hU)]; rfl
  unfold parLb parLb3 parMg
  rw [e2]
  simp only []
  rw [if_pos (pa_sle hpa)]

/-- The delivered reply's sender has no counted reply at the ballot yet. -/
theorem par_fresh (S : Sys) (hS : Inv S) (fr i n : Nat) (hn : (fr, i, n) ∉ S.delivered)
    (p : PreAcceptReply) (hm : (S.sent fr i)[n]? = some (.preAcceptReply p))
    (m' : PreAcceptReply) (hd : S.deliveredMsg fr i (.preAcceptReply m'))
    (hx' : (Msg.preAcceptReply m').instOf = some (parX p)) (hb' : m'.ballot = p.ballot) :
    False := by
  obtain ⟨n', hn', hdl⟩ := hd
  have hp1 : Msg.isPARat (parX p) p.ballot (.preAcceptReply p) = true := by
    simp [Msg.isPARat]
  have hp2 : Msg.isPARat (parX p) p.ballot (.preAcceptReply m') = true := by
    simp only [Msg.isPARat, Msg.instOf, Option.some.injEq] at hx' ⊢
    simp only [decide_eq_true_eq]; exact ⟨hx', hb'⟩
  have hc1 : 1 ≤ S.cnt fr i (Msg.isPARat (parX p) p.ballot) := by
    unfold Sys.cnt
    exact List.length_pos_of_mem (List.mem_filter.mpr ⟨mem_msgs_of_sent S hm, hp1⟩)
  have h1 := (hS.2.parOnce fr i _ _ hc1).1
  have := pos_unique (S.msgs fr i) (Msg.isPARat (parX p) p.ballot)
    (by unfold Sys.cnt at h1; omega) (msgs_of_sent S hm) hp1 (msgs_of_sent S hn') hp2
  subst this; exact hn hdl

/-! ## What every counting branch shares -/

/-- The guards passed on a pre-accepting bookkeeping and the reply `p` (from `fr`, at the
bookkeeping's ballot) is counted: the pre-state facts, and the counted bookkeeping `parLb lb p`
(its kept fields, its counted replies with the new one, its status and ballot, `aeF`). -/
theorem par_common (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered) (p : PreAcceptReply)
    (hm : (S.sent fr i)[n]? = some (.preAcceptReply p)) (w : InstRec) (lb : LbRec)
    (hw : (S.rep i).inst (parX p) = some w) (hlb : w.lb = some lb)
    (hnc : stGe w.status stCOMMITTED = false) (hlt : lb.lastTriedBallot.slt w.bal = false)
    (hb : p.ballot = lb.lastTriedBallot) (hpa : isPA lb.status) :
    fr ≠ i ∧ (∃ v0, S.ev i (.phase1 (parX p) lb.lastTriedBallot v0) ∧ lb.cmds = some v0.cmds) ∧
    lb.preparing = false ∧ w.bal = lb.lastTriedBallot ∧ lb.preAcceptOKs.toNat ≤ 4 ∧
    (parLb lb p).lastTriedBallot = lb.lastTriedBallot ∧ (parLb lb p).cmds = lb.cmds ∧
    (parLb lb p).clientProposals = lb.clientProposals ∧
    (parLb lb p).tryingToPreAccept = lb.tryingToPreAccept ∧ (parLb lb p).preparing = false ∧
    (parLb lb p).prepareReplies = lb.prepareReplies ∧
    (parLb lb p).leaderResponded = lb.leaderResponded ∧
    (parLb lb p).preAcceptsSent = lb.preAcceptsSent ∧ (parLb lb p).acceptOKs = lb.acceptOKs ∧
    (parLb lb p).preAcceptOKs.toNat = lb.preAcceptOKs.toNat + 1 ∧
    (isPA (parLb lb p).status ∨ (parLb lb p).status = stACCEPTED ∨
      isCommitted (parLb lb p).status) ∧
    (1 ≤ lb.preAcceptOKs.toNat → (parLb lb p).status = lb.status) ∧
    (isPA (parLb lb p).status → (parLb lb p).ballot = lb.lastTriedBallot) ∧
    zz (parLb lb p).ballot ≤ zz lb.lastTriedBallot ∧
    ((parLb lb p).status ≠ stNONE → depsOk (parLb lb p).deps) ∧
    (∃ Q : List (Nat × PreAcceptReply), (Q.map (·.1)).Nodup ∧
      Q.length = (parLb lb p).preAcceptOKs.toNat ∧
      ∀ a m', (a, m') ∈ Q → a < nR ∧ a ≠ i ∧
        (S.deliveredMsg a i (.preAcceptReply m') ∨ a = fr ∧ m' = p) ∧
        (Msg.preAcceptReply m').instOf = some (parX p) ∧ m'.ballot = lb.lastTriedBallot ∧
        (isPA (parLb lb p).status → depsLe m'.deps (parLb lb p).deps ∧
          zz m'.seq ≤ zz (parLb lb p).seq ∧
          ((parLb lb p).allEqual = true → m'.seq = (parLb lb p).seq ∧ m'.deps = (parLb lb p).deps))) ∧
    (isPA (parLb lb p).status → (parLb lb p).allEqual = false → ∃ (a a' : Nat)
      (m1 m2 : PreAcceptReply), Msg.preAcceptReply m1 ∈ S.sent a i ∧
      Msg.preAcceptReply m2 ∈ S.sent a' i ∧ parX m1 = parX p ∧ parX m2 = parX p ∧
      m1.ballot = lb.lastTriedBallot ∧ m2.ballot = lb.lastTriedBallot ∧
      (m1.seq ≠ m2.seq ∨ m1.deps ≠ m2.deps)) := by
  have hpm := mem_msgs_of_sent S hm
  have hA := hS.2
  have hfi : fr ≠ i := (hS.1.1.2.2.2.2.2.1 fr i (List.ne_nil_of_mem hpm)).2.2
  have hrrv : Inv.repliesReportVotes S := let ⟨_, _, _, _, _, _, _, _, h, _⟩ := hS.1; h
  have hmw : Inv.msgWf S := hS.1.2.1
  have hlbI : Inv.lbInv S := let ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩ := hS.1; h
  obtain ⟨⟨v0, hv0⟩, hpaP, -, -⟩ := hrrv.2.1 fr i p hpm
  rw [hb] at hv0
  have hcmds := hA.pm.paCmds i hi _ w lb hw hlb hpa v0 hv0
  have hprep : lb.preparing = false := by
    cases h : lb.preparing
    · rfl
    · exact absurd hv0 ((hA.prepNoProp i hi _ w lb hw hlb h).2.1 v0)
  have hbal : w.bal = lb.lastTriedBallot := by
    have h1 := (slt_false _ _).mp hlt
    have h2 := hA.lastLeBal i hi _ w lb hw hlb
    exact zz_inj (by omega)
  obtain ⟨-, a2, -, -, a5, ⟨Q, q1, q2, q3⟩, -, -, -⟩ := hlbI i hi _ w lb hw hlb
  obtain ⟨hpst, hv1, hv2, -⟩ := hA.pm.parSt fr i p hpm
  rw [hb] at hv2
  have hpd : depsOk p.deps := (hmw fr i _ hpm).2 p.deps (by simp [Msg.depsFields])
  have hld : depsOk lb.deps := (hS.1.1.2.1 i hi _ w hw).2.2.2.2.1 lb hlb
    (by rcases hpa with h | h <;> rw [h] <;> decide)
  have hfrQ : fr ∉ Q.map (·.1) := by
    intro h
    obtain ⟨⟨a, m'⟩, hq, ha⟩ := List.mem_map.mp h
    obtain ⟨-, -, hd, hx', hb', -⟩ := q3 a m' hq
    have ha' : a = fr := ha
    rw [ha'] at hd
    exact par_fresh S hS fr i n hn p hm m' hd hx' (by rw [hb', hb])
  have hle4 : lb.preAcceptOKs.toNat ≤ 4 := by
    have := par_nodup_len_le (Q := i :: Q.map (·.1))
      (List.nodup_cons.mpr ⟨fun h => by
        obtain ⟨⟨a, m'⟩, hq, rfl⟩ := List.mem_map.mp h
        exact (q3 a m' hq).2.1 rfl, q1⟩)
      (fun a ha => by
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hi
        · obtain ⟨⟨a, m'⟩, hq, rfl⟩ := List.mem_map.mp ha
          exact (q3 a m' hq).1)
    simp only [List.length_cons, List.length_map, nR] at this
    omega
  have hsucc := par_w64_succ lb.preAcceptOKs (by omega)
  have hpfr : Msg.preAcceptReply p ∈ S.sent fr i := List.mem_of_getElem? hm
  rcases Nat.eq_zero_or_pos lb.preAcceptOKs.toNat with h0 | h0
  · -- no counted reply yet: the reply's vote is taken
    have hz : lb.preAcceptOKs = W64 0 := by
      apply BitVec.eq_of_toNat_eq; rw [h0]; rfl
    have hfresh := hA.pm.paFresh i hi _ w lb hw hlb hpa hz ⟨v0, hv0⟩
    have hU : lb.ballot.slt p.vballot = true := (slt_iff _ _).mpr (by omega)
    rw [parLb_upd lb p hU hpd.1]
    refine ⟨hfi, ⟨v0, hv0, hcmds⟩, hprep, hbal, hle4, rfl, rfl, rfl, rfl, hprep, rfl, rfl, rfl,
      rfl, hsucc, hpst, fun h => by omega, fun h => by rw [(hpaP h).1, hb], hv2, fun _ => hpd,
      ⟨[(fr, p)], by simp, by simp [hsucc, h0], fun a m' hq => ?_⟩, fun _ hae => ?_⟩
    · simp only [List.mem_singleton, Prod.mk.injEq] at hq
      rw [hq.1, hq.2]
      exact ⟨hfr, hfi, Or.inr ⟨rfl, rfl⟩, rfl, hb, fun _ =>
        ⟨depsLe_refl hpd.1, Int.le_refl _, fun _ => ⟨rfl, rfl⟩⟩⟩
    · exact hA.pm.aeF i hi _ w lb hw hlb hpa hae
  · -- counted replies: `lb.ballot` is the ballot, the reply is merged
    have hne : lb.preAcceptOKs ≠ W64 0 := by
      intro h; rw [h] at h0; exact absurd h0 (by decide)
    obtain ⟨hlbb, -, -⟩ := a5 hpa hne
    have hU : lb.ballot.slt p.vballot = false := (slt_false _ _).mpr (by rw [hlbb]; omega)
    rw [parLb_noupd lb p hU hpa]
    obtain ⟨g1, g2, g3, g4, -, -, g7⟩ :=
      merge_spec lb.seq p.seq lb.deps p.deps hld.1 hpd.1
    have hself : lb.seq = p.seq ∧ lb.deps = p.deps →
        mergeAttributes lb.seq lb.deps p.seq p.deps = (lb.seq, lb.deps, true) := by
      rintro ⟨e1, e2⟩; rw [← e1, ← e2]; exact merge_self _ _ hld.1
    have gd := merge_depsOk lb.seq p.seq lb.deps p.deps hld hpd
    generalize mergeAttributes lb.seq lb.deps p.seq p.deps = mg at g1 g2 g3 g4 g7 hself gd ⊢
    refine ⟨hfi, ⟨v0, hv0, hcmds⟩, hprep, hbal, hle4, rfl, rfl, rfl, rfl, hprep, rfl, rfl, rfl,
      rfl, hsucc, Or.inl hpa, fun _ => rfl, fun _ => hlbb,
      show zz lb.ballot ≤ _ by rw [hlbb]; exact Int.le_refl _, fun _ => gd,
      ⟨Q ++ [(fr, p)], ?_, show _ = (lb.preAcceptOKs + 1).toNat by
        rw [hsucc, List.length_append, q2]; rfl, fun a m' hq => ?_⟩, fun _ hae => ?_⟩
    · rw [List.map_append]
      exact List.nodup_append.mpr ⟨q1, by simp, fun a ha b hb' hab => by
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb'
        subst hb'; subst hab; exact hfrQ ha⟩
    · rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨c1, c2, c3, c4, c5, c6⟩ := q3 a m' hq
        obtain ⟨d1, d2, d3⟩ := c6 hpa
        refine ⟨c1, c2, Or.inl c3, c4, c5, fun _ => ⟨depsLe_trans d1 g1, Int.le_trans d2 g3,
          fun hae => ?_⟩⟩
        simp only [Bool.and_eq_true] at hae
        obtain ⟨e1, e2⟩ := d3 hae.1
        rw [hself (g7.mp hae.2)]; exact ⟨e1, e2⟩
      · simp only [List.mem_singleton, Prod.mk.injEq] at hq
        rw [hq.1, hq.2]
        refine ⟨hfr, hfi, Or.inr ⟨rfl, rfl⟩, rfl, hb, fun _ => ⟨g2, g4, fun hae => ?_⟩⟩
        simp only [Bool.and_eq_true] at hae
        have e := g7.mp hae.2
        rw [hself e]; exact ⟨e.1.symm, e.2.symm⟩
    · simp only at hae
      cases hlae : lb.allEqual
      · exact hA.pm.aeF i hi _ w lb hw hlb hpa hlae
      · rw [hlae, Bool.true_and] at hae
        have hdiff : ¬ (lb.seq = p.seq ∧ lb.deps = p.deps) := fun h => by
          rw [g7.mpr h] at hae; exact absurd hae (by decide)
        obtain ⟨⟨a', m'⟩, hq⟩ : ∃ e, e ∈ Q := List.exists_mem_of_length_pos (by omega)
        obtain ⟨-, -, ⟨n', hn', -⟩, hx', hb', c6⟩ := q3 a' m' hq
        obtain ⟨-, -, d3⟩ := c6 hpa
        obtain ⟨e1, e2⟩ := d3 hlae
        simp only [Msg.instOf, Option.some.injEq] at hx'
        refine ⟨fr, a', p, m', hpfr, List.mem_of_getElem? hn', rfl, hx', hb, hb', ?_⟩
        rcases Classical.em (p.seq = m'.seq) with hc1 | hc1
        · rcases Classical.em (p.deps = m'.deps) with hc2 | hc2
          · exact absurd ⟨by rw [← e1, hc1], by rw [← e2, hc2]⟩ hdiff
          · exact Or.inr hc2
        · exact Or.inl hc1

end PARProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
