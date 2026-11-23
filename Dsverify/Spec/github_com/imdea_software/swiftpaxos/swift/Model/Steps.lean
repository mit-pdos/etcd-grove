/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Model/Steps.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Protocol steps as pure transitions of PState that keep PInv: handling a proposal, pre-accepting, accepting, committing (the new leader, report and MSync steps: not yet).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Protocol

@[expose] public section

noncomputable section

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

theorem before_append_of_mem (s u : Seq) (y : CmdId) (h : y ∈ s.map Prod.fst) :
    before (s ++ u) y = before s y ∧ cmdIn (s ++ u) y = cmdIn s y := by
  unfold before cmdIn
  induction s with
  | nil => simp at h
  | cons p s ih =>
    by_cases hp : p.1 = y
    · simp [hp]
    · have h' : y ∈ s.map Prod.fst := by simp at h ⊢; rcases h with h | h; exact absurd h.symm hp; exact h
      obtain ⟨h1, h2⟩ := ih h'
      have hb : (p.1 != y) = true := by simpa using hp
      have hb' : (p.1 == y) = false := by simpa using hp
      simp only [List.cons_append, List.takeWhile_cons, hb, ite_true, List.find?_cons, hb']
      exact ⟨by rw [h1], h2⟩

theorem depsIn_append_of_mem (s u : Seq) (y : CmdId) (h : y ∈ s.map Prod.fst) :
    depsIn (s ++ u) y = depsIn s y := by
  unfold depsIn; obtain ⟨h1, h2⟩ := before_append_of_mem s u y h; rw [h1, h2]

theorem seqOf_mem_fst (S : PState) (l : List CmdId) (y : CmdId) (hy : y ∈ l) (hreg : S.cmds y ≠ none) :
    y ∈ (S.seqOf l).map Prod.fst := by
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hreg
  exact List.mem_map.mpr ⟨(y, c), List.mem_filterMap.mpr ⟨y, hy, by simp [hc]⟩, rfl⟩

theorem RState.locAt_cons (s : RState) (b b' : Nat) (l : List CmdId) :
    ({ s with locR := (b, l) :: s.locR } : RState).locAt b' = if b' = b then l else s.locAt b' := by
  unfold RState.locAt; by_cases h : b' = b
  · subst h; simp
  · simp [List.find?_cons, Ne.symm h, h]

theorem RState.preAt_cons (s : RState) (b b' : Nat) (y x : CmdId) (D : List CmdId) :
    ({ s with preR := ((b, y), D) :: s.preR } : RState).preAt b' x =
      if b' = b ∧ x = y then some D else s.preAt b' x := by
  unfold RState.preAt; by_cases h : b' = b ∧ x = y
  · obtain ⟨rfl, rfl⟩ := h; simp
  · simp only [List.find?_cons]
    have : (((b, y), D).1 == (b', x)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, Prod.mk.injEq]; intro ⟨h1, h2⟩; exact h ⟨h1.symm, h2.symm⟩
    simp [this, h]

theorem RState.pathAt_cons (s : RState) (b b' : Nat) (y x : CmdId) (P : List CmdId) :
    ({ s with pathR := ((b, y), P) :: s.pathR } : RState).pathAt b' x =
      if b' = b ∧ x = y then some P else s.pathAt b' x := by
  unfold RState.pathAt; by_cases h : b' = b ∧ x = y
  · obtain ⟨rfl, rfl⟩ := h; simp
  · simp only [List.find?_cons]
    have : (((b, y), P).1 == (b', x)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, Prod.mk.injEq]; intro ⟨h1, h2⟩; exact h ⟨h1.symm, h2.symm⟩
    simp [this, h]

theorem RState.repAt_cons (s : RState) (b b' : Nat) (R : Report) :
    ({ s with repR := (b, R) :: s.repR } : RState).repAt b' = if b' = b then some R else s.repAt b' := by
  unfold RState.repAt; by_cases h : b' = b
  · subst h; simp
  · simp [List.find?_cons, Ne.symm h, h]

namespace PState

/-- **Step: a replica's run loop handles a proposal** (`handleProposal`): `x` is appended to
replica `r`'s sequence of its ballot `b`. -/
def handle (S : PState) (r b : Nat) (x : CmdId) : PState :=
  { S with
    loc := fun r' b' => if r' = r ∧ b' = b then S.loc r b ++ [x] else S.loc r' b'
    rs := fun r' => { S.rs r' with
      locR := if r' = r then (b, S.loc r b ++ [x]) :: (S.rs r').locR else (S.rs r').locR } }

variable {S : PState} {N : Nat} {fr : Bool}

theorem handle_loc (r b : Nat) (x : CmdId) (r' b' : Nat) :
    ∃ t, (S.handle r b x).loc r' b' = S.loc r' b' ++ t := by
  unfold handle; simp only
  split
  · rename_i h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[x], rfl⟩
  · exact ⟨[], by simp⟩

theorem handle_loc_ne (r b : Nat) (x : CmdId) (r' b' : Nat) (h : ¬ (r' = r ∧ b' = b)) :
    (S.handle r b x).loc r' b' = S.loc r' b' := by
  unfold handle; simp only [h, ite_false]

theorem handle_depsIn (hI : S.PInv N fr) (r b : Nat) (x : CmdId) (r' b' : Nat) (y : CmdId)
    (hy : y ∈ S.loc r' b') :
    depsIn ((S.handle r b x).seqOf ((S.handle r b x).loc r' b')) y = depsIn (S.seqOf (S.loc r' b')) y := by
  obtain ⟨t, ht⟩ := handle_loc (S := S) r b x r' b'
  show depsIn (S.seqOf ((S.handle r b x).loc r' b')) y = _
  rw [ht, seqOf_append]
  exact depsIn_append_of_mem _ _ y (seqOf_mem_fst S _ y hy ((hI.loc_ok r' b').2.1 y hy))

theorem handle_keyPrefix (hI : S.PInv N fr) (r b : Nat) (x : CmdId) (r' b' : Nat) (y : CmdId)
    (hy : y ∈ S.loc r' b') (hyB : y ∉ S.base b') :
    (S.handle r b x).keyPrefix r' b' y = S.keyPrefix r' b' y := by
  obtain ⟨t, ht⟩ := handle_loc (S := S) r b x r' b'
  have hne : S.loc r' b' ≠ [] := fun h => by rw [h] at hy; simp at hy
  have hpre : S.base b' <+: S.loc r' b' := by
    by_cases hb : b' = 0
    · subst hb
      have : S.base 0 = [] := by
        unfold base; cases hs : S.sync 0 with
        | none => rfl
        | some M => have := (hI.sync_ok 0 M hs).1; omega
      rw [this]; exact List.nil_prefix
    · exact (((hI.loc_ok r' b').2.2 hne).2.2 (by omega)).2
  obtain ⟨H, hH⟩ := hpre
  have hyH : y ∈ H := by rw [← hH] at hy; rcases List.mem_append.mp hy with h | h; exact absurd h hyB; exact h
  have e1 : (S.handle r b x).cmds = S.cmds := rfl
  have e2 : (S.handle r b x).base b' = S.base b' := rfl
  have e3 : (S.handle r b x).seqOf = S.seqOf := rfl
  unfold keyPrefix
  rw [e1, e2, e3]
  rw [ht, ← hH]
  simp only [List.append_assoc, List.drop_left]
  rw [seqOf_append]
  have := (before_append_of_mem (S.seqOf H) (S.seqOf t) y
    (seqOf_mem_fst S H y hyH ((hI.loc_ok r' b').2.1 y hy))).1
  unfold before at this; rw [this]

theorem handle_mem {r b : Nat} {x : CmdId} {r' b' : Nat} {y : CmdId} (h : y ∈ S.loc r' b') :
    y ∈ (S.handle r b x).loc r' b' := by
  obtain ⟨t, ht⟩ := handle_loc (S := S) r b x r' b'; rw [ht]; exact List.mem_append_left _ h

/-- Handling a proposal keeps the invariant: `x` registered and new in `r`'s sequence of `r`'s
ballot `b`, which starts with `b`'s `MSync`. -/
theorem PInv_handle (hI : S.PInv N fr) (r b : Nat) (x : CmdId) (hx : S.cmds x ≠ none)
    (hn : x ∉ S.loc r b) (hr : r < N) (hbal : (S.rs r).ballot = b)
    (hbase : b > 0 → S.sync b ≠ none ∧ S.base b <+: S.loc r b) : (S.handle r b x).PInv N fr := by
  have hsame : ∀ r' b', ¬ (r' = r ∧ b' = b) → (S.handle r b x).loc r' b' = S.loc r' b' :=
    fun r' b' h => handle_loc_ne r b x r' b' h
  -- a report's own ballots are below r's present one
  have hrep_lt : ∀ r'' b'' R, S.rep r'' b'' = some R → r'' = r → b'' ≤ b := by
    intro r'' b'' R h hr''; subst hr''
    have := (PState.repOk_parts (hI.rep_ok _ _ _ h)).1; omega
  have hord : ∀ c y, y ∈ S.ord N c → depsIn ((S.handle r b x).ordSeq N c) y = depsIn (S.ordSeq N c) y :=
    fun c y hy => handle_depsIn hI r b x _ c y hy
  refine ⟨?_, hI.rs_ok, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨hI.G_ok.1, hI.G_ok.2⟩⟩
  · -- loc_ok
    intro r' b'
    by_cases h : r' = r ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h
      have e : (S.handle r' b' x).loc r' b' = S.loc r' b' ++ [x] := by unfold handle; simp
      rw [e]
      refine ⟨List.nodup_append.mpr ⟨(hI.loc_ok _ _).1, by simp, by
        intro a ha c hc; simp at hc; subst hc; intro h; subst h; exact hn ha⟩, ?_, ?_⟩
      · intro y hy; rcases List.mem_append.mp hy with h | h
        · exact (hI.loc_ok _ _).2.1 y h
        · simp at h; subst h; exact hx
      · intro _; refine ⟨hr, show (S.rs r').ballot ≥ b' by omega, fun hb => ⟨(hbase hb).1, ?_⟩⟩
        exact (hbase hb).2.trans (List.prefix_append _ _)
    · rw [hsame r' b' h]; exact hI.loc_ok r' b'
  · -- acc_ok
    intro r' b' y hy
    obtain ⟨h1, h2, h3, h4, h5⟩ := hI.acc_ok r' b' y hy
    exact ⟨h1, handle_mem h2, handle_mem h3, h4, by rw [hord b' y h3]; exact h5⟩
  · -- pre_ok
    intro r' b' y D hy
    obtain ⟨h1, h2, h3, h4, h5⟩ := hI.pre_ok r' b' y D hy
    exact ⟨h1, h2, handle_mem h3, by rw [handle_depsIn hI r b x r' b' y h3]; exact h4, h5⟩
  · -- path_ok
    intro r' b' y P hy
    obtain ⟨h1, h2, h3, h4, h5⟩ := hI.path_ok r' b' y P hy
    have e := handle_keyPrefix hI r b x r' b' y h1 h2
    exact ⟨handle_mem h1, h2, h3, by rw [e]; exact h4, by rw [e]; exact h5⟩
  · -- com_ok
    intro r' b' y hy
    obtain ⟨h1, h2, h3, h4⟩ := hI.com_ok r' b' y hy
    exact ⟨h1, h2, handle_mem h3, h4⟩
  · -- rep_ok
    intro r'' b'' R hR
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := PState.repOk_parts (hI.rep_ok r'' b'' R hR)
    have hnot : ∀ c', c' < b'' → (S.handle r b x).loc r'' c' = S.loc r'' c' := by
      intro c' hc'; apply hsame; rintro ⟨rfl, rfl⟩; have := hrep_lt _ _ _ hR rfl; omega
    have hc := hnot R.cbal p2
    refine ⟨p1, p2, p3, fun c' y h1 h2 => ?_, p5, p6, ?_, ?_, ?_⟩
    · obtain ⟨a, b2, c2, d⟩ := p4 c' y h1 h2; exact ⟨a, b2, c2, by rw [hnot c' h2]; exact d⟩
    · intro hL y hy
      apply p7 hL
      have : ¬ (leaderOf N R.cbal = r ∧ R.cbal = b) := by
        rintro ⟨h1, h2⟩; rw [← hL] at h1; have := hrep_lt _ _ _ hR h1; omega
      show y ∈ S.loc (leaderOf N R.cbal) R.cbal
      rw [← hsame _ _ this]; exact hy
    · show ∃ B, B.Perm (S.base R.cbal) ∧ R.entries.map (·.id) = B ++ ((S.handle r b x).loc r'' R.cbal).drop _
      rw [hc]; exact p8
    · intro e he
      obtain ⟨q1, q2, q3, q4, q5, q6⟩ := p9 e he
      refine ⟨q1, by rw [hc]; exact q2, q3, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · obtain ⟨a, b2, c2⟩ := q4 h
        exact ⟨a, handle_mem b2, by rw [hord _ _ b2]; exact c2⟩
      · rcases q5 h with ⟨a, b2, c2⟩ | d
        · exact Or.inl ⟨a, handle_mem b2, by rw [hord _ _ b2]; exact c2⟩
        · exact Or.inr d
      · intro d hd; have := q6 h d hd
        show d ∈ depsIn (S.seqOf ((S.handle r b x).loc r'' R.cbal)) e.id
        rw [hc]; exact this
  · -- sync_ok
    intro b' M hM
    obtain ⟨h1, h2, h3, h4⟩ := hI.sync_ok b' M hM
    obtain ⟨t, ht⟩ := handle_loc (S := S) r b x (leaderOf N b') b'
    refine ⟨h1, h2, ?_, h4⟩
    show S.base b' <+: (S.handle r b x).loc (leaderOf N b') b'
    rw [ht]; exact h3.trans (List.prefix_append _ _)
  · -- rows_ok
    intro r' b'
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hI.rows_ok r' b'
    refine ⟨?_, o2, o3, o4, o5, o6⟩
    show (if r' = r ∧ b' = b then S.loc r b ++ [x] else S.loc r' b') =
      ({ S.rs r' with locR := if r' = r then (b, S.loc r b ++ [x]) :: (S.rs r').locR
          else (S.rs r').locR } : RState).locAt b'
    by_cases hr : r' = r
    · subst hr; simp only [ite_true]; rw [RState.locAt_cons]
      by_cases hb : b' = b
      · simp [hb]
      · simp only [hb, and_false, ite_false]; exact o1
    · simp only [hr, false_and, ite_false]; exact o1


/-- **Step: an acceptance** (`fastAckFromLeader` at a follower, or the leader's own): `r`
accepts `y` in its ballot `b`. -/
def accept (S : PState) (r b : Nat) (y : CmdId) : PState :=
  { S with
    acc := fun r' b' y' => S.acc r' b' y' ∨ (r' = r ∧ b' = b ∧ y' = y)
    rs := fun r' => { S.rs r' with
      accR := if r' = r then (b, y) :: (S.rs r').accR else (S.rs r').accR } }

/-- Accepting keeps the invariant: the leader's command, which `r` handled, its dependencies
accepted or committed first (N2). -/
theorem PInv_accept (hI : S.PInv N fr) (r b : Nat) (y : CmdId) (hr : r < N) (hbal : (S.rs r).ballot = b)
    (hloc : y ∈ S.loc r b) (hord : y ∈ S.ord N b)
    (hN2 : r ≠ leaderOf N b → ∀ d ∈ depsIn (S.ordSeq N b) y, S.acc r b d ∨ S.com r b d) :
    (S.accept r b y).PInv N fr := by
  have hrep_lt : ∀ r'' b'' R, S.rep r'' b'' = some R → r'' = r → b'' ≤ b := by
    intro r'' b'' R h hr''; subst hr''
    have := (PState.repOk_parts (hI.rep_ok _ _ _ h)).1; omega
  refine ⟨hI.loc_ok, hI.rs_ok, ?_, hI.pre_ok, hI.path_ok, ?_, ?_, hI.sync_ok, ?_, hI.G_ok⟩
  · intro r' b' y' h
    rcases h with h | ⟨rfl, rfl, rfl⟩
    · obtain ⟨a1, a2, a3, a4, a5⟩ := hI.acc_ok r' b' y' h
      exact ⟨a1, a2, a3, a4, fun hne d hd => (a5 hne d hd).imp Or.inl id⟩
    · exact ⟨hr, hloc, hord, show (S.rs r').ballot ≥ b' by omega,
        fun hne d hd => (hN2 hne d hd).imp Or.inl id⟩
  · intro r' b' y' h
    obtain ⟨a1, a2, a3, a4⟩ := hI.com_ok r' b' y' h
    exact ⟨a1, a2, a3, a4.imp id (fun h => h.imp Or.inl id)⟩
  · intro r'' b'' R hR
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := PState.repOk_parts (hI.rep_ok r'' b'' R hR)
    have hnew : ∀ c' y', c' < b'' → (r'' = r ∧ c' = b ∧ y' = y) → False := by
      rintro c' y' hc ⟨rfl, rfl, -⟩; have := hrep_lt _ _ _ hR rfl; omega
    refine ⟨p1, p2, p3, fun c' y' h1 h2 => ?_, fun y' h => ?_, p6, p7, p8, fun e he => ?_⟩
    · obtain ⟨a, b2, c2, d⟩ := p4 c' y' h1 h2
      exact ⟨fun h => h.elim a (hnew c' y' h2), b2, c2, d⟩
    · rcases h with (h | h) | h
      · exact p5 y' (Or.inl h)
      · exact absurd h (hnew _ _ p2)
      · exact p5 y' (Or.inr h)
    · obtain ⟨q1, q2, q3, q4, q5, q6⟩ := p9 e he
      exact ⟨q1, q2, q3, fun h => let r := q4 h; ⟨r.1.imp Or.inl id, r.2⟩, q5, q6⟩
  · -- rows_ok
    intro r' b'
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hI.rows_ok r' b'
    refine ⟨o1, ?_, o3, o4, o5, o6⟩
    intro x'
    show (S.acc r' b' x' ∨ (r' = r ∧ b' = b ∧ x' = y)) ↔
      (b', x') ∈ (if r' = r then (b, y) :: (S.rs r').accR else (S.rs r').accR)
    rw [o2 x']
    by_cases hr : r' = r
    · subst hr; simp only [true_and, ite_true, List.mem_cons, Prod.mk.injEq]
      exact Or.comm
    · simp [hr]


/-- **Step: a commit** (the fast or slow path's handler, or the `MSync`'s commands). -/
def commit (S : PState) (r b : Nat) (y : CmdId) : PState :=
  { S with
    com := fun r' b' y' => S.com r' b' y' ∨ (r' = r ∧ b' = b ∧ y' = y)
    rs := fun r' => { S.rs r' with
      comR := if r' = r then (b, y) :: (S.rs r').comR else (S.rs r').comR } }

/-- Committing keeps the invariant: by the leader, of an accepted command, or of the base. -/
theorem PInv_commit (hI : S.PInv N fr) (r b : Nat) (y : CmdId) (hr : r < N) (hbal : (S.rs r).ballot = b)
    (hloc : y ∈ S.loc r b) (hwhy : r = leaderOf N b ∨ S.acc r b y ∨ y ∈ S.base b) :
    (S.commit r b y).PInv N fr := by
  have hrep_lt : ∀ r'' b'' R, S.rep r'' b'' = some R → r'' = r → b'' ≤ b := by
    intro r'' b'' R h hr''; subst hr''
    have := (PState.repOk_parts (hI.rep_ok _ _ _ h)).1; omega
  refine ⟨hI.loc_ok, hI.rs_ok, ?_, hI.pre_ok, hI.path_ok, ?_, ?_, hI.sync_ok, ?_, hI.G_ok⟩
  · intro r' b' y' h
    obtain ⟨a1, a2, a3, a4, a5⟩ := hI.acc_ok r' b' y' h
    exact ⟨a1, a2, a3, a4, fun hne d hd => (a5 hne d hd).imp id Or.inl⟩
  · intro r' b' y' h
    rcases h with h | ⟨rfl, rfl, rfl⟩
    · exact hI.com_ok r' b' y' h
    · exact ⟨hr, show (S.rs r').ballot ≥ b' by omega, hloc, hwhy⟩
  · intro r'' b'' R hR
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := PState.repOk_parts (hI.rep_ok r'' b'' R hR)
    have hnew : ∀ c' y', c' < b'' → (r'' = r ∧ c' = b ∧ y' = y) → False := by
      rintro c' y' hc ⟨rfl, rfl, -⟩; have := hrep_lt _ _ _ hR rfl; omega
    refine ⟨p1, p2, p3, fun c' y' h1 h2 => ?_, fun y' h => ?_, p6, p7, p8, fun e he => ?_⟩
    · obtain ⟨a, b2, c2, d⟩ := p4 c' y' h1 h2
      exact ⟨a, b2, fun h => h.elim c2 (hnew c' y' h2), d⟩
    · rcases h with h | (h | h)
      · exact p5 y' (Or.inl h)
      · exact p5 y' (Or.inr h)
      · exact absurd h (hnew _ _ p2)
    · obtain ⟨q1, q2, q3, q4, q5, q6⟩ := p9 e he
      exact ⟨q1, q2, q3, fun h => let r := q4 h; ⟨r.1.imp id Or.inl, r.2⟩, q5, q6⟩
  · -- rows_ok
    intro r' b'
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hI.rows_ok r' b'
    refine ⟨o1, o2, o3, o4, ?_, o6⟩
    intro x'
    show (S.com r' b' x' ∨ (r' = r ∧ b' = b ∧ x' = y)) ↔
      (b', x') ∈ (if r' = r then (b, y) :: (S.rs r').comR else (S.rs r').comR)
    rw [o5 x']
    by_cases hr : r' = r
    · subst hr; simp only [true_and, ite_true, List.mem_cons, Prod.mk.injEq]
      exact Or.comm
    · simp [hr]


/-- **Step: a pre-acceptance** (`handlePropose` at a fast-quorum member): `r` pre-accepts `y`
in `b` with dependencies `D` and path `P`. -/
def preaccept (S : PState) (r b : Nat) (y : CmdId) (D P : List CmdId) : PState :=
  { S with
    pre := fun r' b' y' => if r' = r ∧ b' = b ∧ y' = y then some D else S.pre r' b' y'
    path := fun r' b' y' => if r' = r ∧ b' = b ∧ y' = y then some P else S.path r' b' y'
    rs := fun r' => { S.rs r' with
      preR := if r' = r then ((b, y), D) :: (S.rs r').preR else (S.rs r').preR
      pathR := if r' = r then ((b, y), P) :: (S.rs r').pathR else (S.rs r').pathR } }

/-- Pre-accepting keeps the invariant: a fast-quorum member's own dependencies, its path as
`HashLog.Append` computed it (its key's commands it handled, the leader's exactly). -/
theorem PInv_preaccept (hI : S.PInv N fr) (r b : Nat) (y : CmdId) (D P : List CmdId)
    (hAQ : r ∈ AQ N b) (hbal : (S.rs r).ballot = b) (hloc : y ∈ S.loc r b)
    (hD : D = depsIn (S.seqOf (S.loc r b)) y) (hB : y ∉ S.base b) (hlast : P.getLast? = some y)
    (hLP : r = leaderOf N b → P = S.keyPrefix r b y) (hP : ∀ z ∈ S.keyPrefix r b y, z ∈ P) :
    (S.preaccept r b y D P).PInv N fr := by
  have hrep_lt : ∀ r'' b'' R, S.rep r'' b'' = some R → r'' = r → b'' ≤ b := by
    intro r'' b'' R h hr''; subst hr''
    have := (PState.repOk_parts (hI.rep_ok _ _ _ h)).1; omega
  refine ⟨hI.loc_ok, hI.rs_ok, hI.acc_ok, ?_, ?_, hI.com_ok, ?_, hI.sync_ok, ?_, hI.G_ok⟩
  · intro r' b' y' D' h
    show r' ∈ AQ N b' ∧ (S.rs r').ballot ≥ b' ∧ y' ∈ S.loc r' b' ∧ D' = depsIn (S.seqOf (S.loc r' b')) y' ∧
      (if r' = r ∧ b' = b ∧ y' = y then some P else S.path r' b' y') ≠ none
    have h' : (if r' = r ∧ b' = b ∧ y' = y then some D else S.pre r' b' y') = some D' := h
    by_cases hc : r' = r ∧ b' = b ∧ y' = y
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      simp at h'; subst h'
      exact ⟨hAQ, by omega, hloc, hD, by simp⟩
    · rw [if_neg hc] at h'; rw [if_neg hc]; exact hI.pre_ok r' b' y' D' h'
  · intro r' b' y' P' h
    have h' : (if r' = r ∧ b' = b ∧ y' = y then some P else S.path r' b' y') = some P' := h
    by_cases hc : r' = r ∧ b' = b ∧ y' = y
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      simp at h'; subst h'
      exact ⟨hloc, hB, hlast, hLP, hP⟩
    · rw [if_neg hc] at h'; exact hI.path_ok r' b' y' P' h'
  · intro r'' b'' R hR
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := PState.repOk_parts (hI.rep_ok r'' b'' R hR)
    have hnew : ∀ c' y', c' < b'' → ¬ (r'' = r ∧ c' = b ∧ y' = y) := by
      rintro c' y' hc ⟨rfl, rfl, -⟩; have := hrep_lt _ _ _ hR rfl; omega
    refine ⟨p1, p2, p3, fun c' y' h1 h2 => ?_, p5, fun y' D' h => ?_, p7, p8, fun e he => ?_⟩
    · obtain ⟨a, b2, c2, d⟩ := p4 c' y' h1 h2
      refine ⟨a, ?_, c2, d⟩
      show (if r'' = r ∧ c' = b ∧ y' = y then some D else S.pre r'' c' y') = none
      rw [if_neg (hnew c' y' h2)]; exact b2
    · have h' : (if r'' = r ∧ R.cbal = b ∧ y' = y then some D else S.pre r'' R.cbal y') = some D' := h
      rw [if_neg (hnew _ y' p2)] at h'; exact p6 y' D' h'
    · obtain ⟨q1, q2, q3, q4, q5, q6⟩ := p9 e he
      refine ⟨q1, q2, q3, q4, fun h => ?_, q6⟩
      rcases q5 h with h' | h'
      · exact Or.inl h'
      · right
        show (if r'' = r ∧ R.cbal = b ∧ e.id = y then some D else S.pre r'' R.cbal e.id) = some e.dep
        rw [if_neg (hnew _ e.id p2)]; exact h'
  · -- rows_ok
    intro r' b'
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hI.rows_ok r' b'
    refine ⟨o1, o2, fun x' => ?_, fun x' => ?_, o5, o6⟩
    · by_cases hr : r' = r
      · subst hr
        simp only [preaccept, ite_true, true_and, RState.preAt, List.find?_cons]
        by_cases h : b' = b ∧ x' = y
        · obtain ⟨rfl, rfl⟩ := h; simp
        · have : ((b, y) == (b', x')) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq, Prod.mk.injEq]; intro ⟨h1, h2⟩; exact h ⟨h1.symm, h2.symm⟩
          simp only [h, ite_false, this]; exact o3 x'
      · simp only [preaccept, hr, false_and, ite_false]; exact o3 x'
    · by_cases hr : r' = r
      · subst hr
        simp only [preaccept, ite_true, true_and, RState.pathAt, List.find?_cons]
        by_cases h : b' = b ∧ x' = y
        · obtain ⟨rfl, rfl⟩ := h; simp
        · have : ((b, y) == (b', x')) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq, Prod.mk.injEq]; intro ⟨h1, h2⟩; exact h ⟨h1.symm, h2.symm⟩
          simp only [h, ite_false, this]; exact o4 x'
      · simp only [preaccept, hr, false_and, ite_false]; exact o4 x'

/-- **Step: a new ballot** (`handleNewLeader`): `r` moves to a higher ballot, recovering. -/
def newBallot (S : PState) (r b' : Nat) : PState :=
  { S with rs := fun r' => { S.rs r' with
      ballot := if r' = r then b' else (S.rs r').ballot
      normal := if r' = r then false else (S.rs r').normal } }

theorem newBallot_ge (S : PState) (r b' : Nat) (h : (S.rs r).ballot ≤ b') (r' : Nat) :
    (S.rs r').ballot ≤ ((S.newBallot r b').rs r').ballot := by
  unfold newBallot; simp only
  by_cases e : r' = r
  · subst e; simp only [ite_true]; exact h
  · simp only [e, ite_false]; exact Nat.le_refl _

/-- Moving to a higher ballot keeps the invariant. -/
theorem PInv_newBallot (hI : S.PInv N fr) (r b' : Nat) (h : (S.rs r).ballot ≤ b') :
    (S.newBallot r b').PInv N fr := by
  have ge := newBallot_ge S r b' h
  refine ⟨fun r'' b => ?_, fun r'' => ?_, fun r'' b y hy => ?_, fun r'' b y D hy => ?_, hI.path_ok,
    fun r'' b y hy => ?_, fun r'' b R hR => ?_, fun b M hM => ?_, hI.rows_ok, hI.G_ok⟩
  · obtain ⟨a1, a2, a3⟩ := hI.loc_ok r'' b
    exact ⟨a1, a2, fun hn => let x := a3 hn; ⟨x.1, Nat.le_trans x.2.1 (ge r''), x.2.2⟩⟩
  · show ((S.newBallot r b').rs r'').cballot ≤ ((S.newBallot r b').rs r'').ballot ∧ _
    unfold newBallot; simp only
    by_cases e : r'' = r
    · subst e; simp only [ite_true]; exact ⟨Nat.le_trans (hI.rs_ok r'').1 h, by simp⟩
    · simp only [e, ite_false]; exact hI.rs_ok r''
  · obtain ⟨a1, a2, a3, a4, a5⟩ := hI.acc_ok r'' b y hy
    exact ⟨a1, a2, a3, Nat.le_trans a4 (ge r''), a5⟩
  · obtain ⟨a1, a2, a3⟩ := hI.pre_ok r'' b y D hy
    exact ⟨a1, Nat.le_trans a2 (ge r''), a3⟩
  · obtain ⟨a1, a2, a3⟩ := hI.com_ok r'' b y hy
    exact ⟨a1, Nat.le_trans a2 (ge r''), a3⟩
  · obtain ⟨p1, p2⟩ := PState.repOk_parts (hI.rep_ok r'' b R hR)
    exact ⟨Nat.le_trans p1 (ge r''), p2⟩
  · obtain ⟨a1, a2, a3⟩ := hI.sync_ok b M hM
    exact ⟨a1, Nat.le_trans a2 (ge _), a3⟩

/-- **Step: a report** (`fillNewLeaderAckN`): `r`'s report for `b'`. -/
def report (S : PState) (r b' : Nat) (R : Report) : PState :=
  { S with
    rep := fun r' b => if r' = r ∧ b = b' then some R else S.rep r' b
    rs := fun r' => { S.rs r' with
      repR := if r' = r then (b', R) :: (S.rs r').repR else (S.rs r').repR } }

/-- Reporting (once per ballot, truthfully) keeps the invariant. -/
theorem PInv_report (hI : S.PInv N fr) (r b' : Nat) (R : Report) (hnone : S.rep r b' = none)
    (hok : S.repOk N r b' R) : (S.report r b' R).PInv N fr := by
  refine ⟨hI.loc_ok, hI.rs_ok, hI.acc_ok, hI.pre_ok, hI.path_ok, hI.com_ok, ?_, ?_, ?_, hI.G_ok⟩
  · intro r'' b R' h
    have h' : (if r'' = r ∧ b = b' then some R else S.rep r'' b) = some R' := h
    by_cases hc : r'' = r ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := hc; simp at h'; subst h'; exact hok
    · rw [if_neg hc] at h'; exact hI.rep_ok r'' b R' h'
  · intro b M hM
    obtain ⟨a1, a2, a3, reps, a4, a5, a6⟩ := hI.sync_ok b M hM
    refine ⟨a1, a2, a3, reps, a4, fun p hp => ?_, a6⟩
    show (if p.1 = r ∧ b = b' then some R else S.rep p.1 b) = some p.2
    by_cases hc : p.1 = r ∧ b = b'
    · obtain ⟨h1, rfl⟩ := hc; have := a5 p hp; rw [h1, hnone] at this; simp at this
    · rw [if_neg hc]; exact a5 p hp
  · -- rows_ok
    intro r' b''
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hI.rows_ok r' b''
    refine ⟨o1, o2, o3, o4, o5, ?_⟩
    show (if r' = r ∧ b'' = b' then some R else S.rep r' b'') =
      ({ S.rs r' with repR := if r' = r then (b', R) :: (S.rs r').repR else (S.rs r').repR } : RState).repAt b''
    by_cases hr : r' = r
    · subst hr; simp only [ite_true, true_and]; rw [RState.repAt_cons]; split <;> simp_all
    · simp only [hr, false_and, ite_false]; exact o6


/-! ### The recovery's end: the new leader computes the `MSync` (MR1), a replica takes it (MR2) -/

theorem recOrder_nodup (k : Kept) (ids : List CmdId) : (recOrder k ids).Nodup := by
  rw [recOrder_eq]
  have : ∀ n, (iter (recOrderStep k ids) n []).Nodup := by
    intro n
    induction n with
    | zero => simp [iter]
    | succ n ih =>
      rw [iter_succ']
      generalize iter (recOrderStep k ids) n [] = pl at ih ⊢
      unfold recOrderStep; dsimp only
      split
      · rename_i c x hc
        have := (List.mem_filter.mp (List.mem_of_find?_eq_some hc)).2
        refine List.nodup_append.mpr ⟨ih, by simp, ?_⟩
        intro a ha b hb; simp at hb; subst hb; intro e; subst e; simp [ha] at this
      · rename_i c hn hc
        have := (List.mem_filter.mp (List.mem_of_mem_head? hc)).2
        refine List.nodup_append.mpr ⟨ih, by simp, ?_⟩
        intro a ha b hb; simp at hb; subst hb; intro e; subst e; simp [ha] at this
      · exact ih
  exact this _

/-- The commands of a recovered `MSync`'s order are registered. -/
theorem recover_reg (hI : S.PInv N fr) {b' : Nat} {reps : List (Nat × Report)}
    (hrep : ∀ p ∈ reps, S.rep p.1 b' = some p.2) (x : CmdId)
    (hx : x ∈ syncOrder (recoverSync N reps)) : S.cmds x ≠ none := by
  let C := mkCtx hI hrep
  have h1 := recOrder_sub _ _ x hx
  unfold sortIds at h1; rw [List.mem_mergeSort] at h1
  rw [C.sync_eq, C.cs_eq] at h1
  have := congrArg (List.map Prod.fst) (lkAlong_ids (S.seqOf (recOrder C.k4 C.ids)))
  rw [List.map_map] at this
  have h2 : x ∈ (S.seqOf (recOrder C.k4 C.ids)).map Prod.fst := by
    rw [← this]; exact h1
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h2
  rw [(Ctx.mem_seqOf hq).1]; simp

/-- **Step MR1: the new leader of `b'` computes the `MSync` `M` and takes it** (its sequence of
`b'` is `M`'s order). -/
def computeSync (S : PState) (N b' : Nat) (M : SyncMsg) : PState :=
  { S with
    sync := fun b => if b = b' then some M else S.sync b
    loc := fun r b => if r = leaderOf N b' ∧ b = b' then syncOrder M else S.loc r b
    rs := fun r' => { S.rs r' with
      locR := if r' = leaderOf N b' then (b', syncOrder M) :: (S.rs r').locR else (S.rs r').locR } }

theorem PInv_computeSync (hI : S.PInv N fr) (b' : Nat) (M : SyncMsg) (reps : List (Nat × Report))
    (hb : 0 < b') (hnone : S.sync b' = none)
    (hL : (S.rs (leaderOf N b')).ballot = b' ∧ ¬ (S.rs (leaderOf N b')).normal)
    (hmaj : isMajority N (reps.map Prod.fst)) (hrep : ∀ p ∈ reps, S.rep p.1 b' = some p.2)
    (hM : M = recoverSync N reps) : (S.computeSync N b' M).PInv N fr := by
  -- nothing was done in b' (no MSync yet)
  have F0 : ∀ r, S.loc r b' = [] := by
    intro r; apply Classical.byContradiction; intro hne
    exact ((hI.loc_ok r b').2.2 hne).2.2 hb |>.1 hnone
  have hloc' : ∀ r b, b ≠ b' → (S.computeSync N b' M).loc r b = S.loc r b := by
    intro r b hbb; show (if r = leaderOf N b' ∧ b = b' then _ else _) = _; simp [hbb]
  have hsync' : ∀ b, b ≠ b' → (S.computeSync N b' M).sync b = S.sync b := by
    intro b hbb; show (if b = b' then _ else _) = _; simp [hbb]
  have hbase' : ∀ b, b ≠ b' → (S.computeSync N b' M).base b = S.base b := by
    intro b hbb; unfold PState.base; rw [hsync' b hbb]
  have hbaseb : (S.computeSync N b' M).base b' = syncOrder M := by
    unfold PState.base; show (((if b' = b' then some M else S.sync b').map syncOrder).getD []) = _; simp
  have hlocL : (S.computeSync N b' M).loc (leaderOf N b') b' = syncOrder M := by
    show (if _ ∧ _ then _ else _) = _; simp
  have hlocr : ∀ r, r ≠ leaderOf N b' → (S.computeSync N b' M).loc r b' = [] := by
    intro r hr; show (if r = leaderOf N b' ∧ b' = b' then _ else _) = _; simp [hr, F0 r]
  have hN : 0 < N := by
    obtain ⟨-, hlt, hlen⟩ := hmaj
    cases hr : reps.map Prod.fst with
    | nil => rw [hr] at hlen; simp at hlen
    | cons r _ => have := hlt r (by rw [hr]; simp); omega
  -- an object of a ballot other than b' (where nothing was done)
  have notb' : ∀ r b x, x ∈ S.loc r b → b ≠ b' := by
    intro r b x hx e; subst e; rw [F0 r] at hx; simp at hx
  have hreg' : (S.computeSync N b' M).seqOf = S.seqOf := rfl
  have hkey : ∀ r b x, b ≠ b' → (S.computeSync N b' M).keyPrefix r b x = S.keyPrefix r b x := by
    intro r b x hbb
    have e1 : (S.computeSync N b' M).cmds = S.cmds := rfl
    unfold PState.keyPrefix; rw [e1, hreg', hloc' r b hbb, hbase' b hbb]
  have hord : ∀ b, b ≠ b' → (S.computeSync N b' M).ord N b = S.ord N b := fun b h => hloc' _ b h
  refine ⟨fun r b => ?_, hI.rs_ok, fun r b x hx => ?_, fun r b x D hx => ?_, fun r b x P hx => ?_,
    fun r b x hx => ?_, fun r b R hR => ?_, fun b M' hM' => ?_, fun r b => ?_, hI.G_ok⟩
  · -- loc_ok
    by_cases h : r = leaderOf N b' ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := h
      rw [hlocL]
      refine ⟨by unfold syncOrder; exact recOrder_nodup _ _, fun y hy => ?_, fun _ => ⟨Nat.mod_lt _ hN,
        show (S.rs _).ballot ≥ _ by omega, fun _ => ⟨by show (if _ = _ then _ else _) ≠ none; simp,
        by rw [hbaseb]; exact List.prefix_refl _⟩⟩⟩
      rw [hM] at hy; exact recover_reg hI hrep y hy
    · have hl : (S.computeSync N b' M).loc r b = S.loc r b := by
        show (if _ then _ else _) = _; rw [if_neg h]
      rw [hl]
      obtain ⟨a1, a2, a3⟩ := hI.loc_ok r b
      refine ⟨a1, a2, fun hn => ?_⟩
      have hbb : b ≠ b' := fun e => hn (by rw [e, F0 r])
      obtain ⟨c1, c2, c3⟩ := a3 hn
      exact ⟨c1, c2, fun hb0 => by rw [hsync' b hbb, hbase' b hbb]; exact c3 hb0⟩
  · -- acc_ok
    obtain ⟨a1, a2, a3, a4, a5⟩ := hI.acc_ok r b x hx
    have hbb := notb' r b x a2
    exact ⟨a1, by rw [hloc' r b hbb]; exact a2, by rw [hord b hbb]; exact a3, a4,
      by rw [show (S.computeSync N b' M).ordSeq N b = S.ordSeq N b from by
        unfold PState.ordSeq; rw [hreg', hord b hbb]]; exact a5⟩
  · -- pre_ok
    obtain ⟨a1, a2, a3, a4, a5⟩ := hI.pre_ok r b x D hx
    have hbb := notb' r b x a3
    exact ⟨a1, a2, by rw [hloc' r b hbb]; exact a3, by rw [hreg', hloc' r b hbb]; exact a4, a5⟩
  · -- path_ok
    obtain ⟨a1, a2, a3, a4, a5⟩ := hI.path_ok r b x P hx
    have hbb := notb' r b x a1
    exact ⟨by rw [hloc' r b hbb]; exact a1, by rw [hbase' b hbb]; exact a2, a3,
      by rw [hkey r b x hbb]; exact a4, by rw [hkey r b x hbb]; exact a5⟩
  · -- com_ok
    obtain ⟨a1, a2, a3, a4⟩ := hI.com_ok r b x hx
    have hbb := notb' r b x a3
    exact ⟨a1, a2, by rw [hloc' r b hbb]; exact a3, by rw [hbase' b hbb]; exact a4⟩
  · -- rep_ok
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := PState.repOk_parts (hI.rep_ok r b R hR)
    have hc : R.cbal ≠ b' := by
      intro e; have := p3 (by omega); rw [e, hnone] at this; obtain ⟨_, h, _⟩ := this; simp at h
    have hcl := hloc' r R.cbal hc
    refine ⟨p1, p2, fun h0 => by rw [hsync' _ hc]; exact p3 h0, fun c' y h1 h2 => ?_, p5, p6,
      fun hL' y hy => p7 hL' y (by rw [hord _ hc] at hy; exact hy), by rw [hbase' _ hc, hcl]; exact p8,
      fun e he => ?_⟩
    · obtain ⟨a, b2, c2, d⟩ := p4 c' y h1 h2
      refine ⟨a, b2, c2, ?_⟩
      by_cases hc' : c' = b'
      · subst hc'
        by_cases hrL : r = leaderOf N c'
        · subst hrL; have := p1; omega
        · rw [hlocr r hrL]
      · rw [hloc' r c' hc']; exact d
    · obtain ⟨q1, q2, q3, q4, q5, q6⟩ := p9 e he
      have hos : (S.computeSync N b' M).ordSeq N R.cbal = S.ordSeq N R.cbal := by
        unfold PState.ordSeq; rw [hreg', hord _ hc]
      refine ⟨q1, by rw [hcl]; exact q2, q3, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · rw [hord _ hc, hos]; exact q4 h
      · rw [hord _ hc, hos]; exact q5 h
      · rw [hreg', hcl]; exact q6 h
  · -- sync_ok
    by_cases hbb : b = b'
    · subst hbb
      have : M' = M := by
        have h' : (if b = b then some M else S.sync b) = some M' := hM'; simp at h'; exact h'.symm
      subst this
      refine ⟨hb, show (S.rs _).ballot ≥ _ by omega, ?_, reps, hmaj, hrep, hM⟩
      rw [hbaseb]; show syncOrder M' <+: (S.computeSync N b M').loc (leaderOf N b) b
      rw [hlocL]; exact List.prefix_refl _
    · rw [hsync' b hbb] at hM'
      obtain ⟨a1, a2, a3, a4⟩ := hI.sync_ok b M' hM'
      refine ⟨a1, a2, ?_, a4⟩
      rw [hbase' b hbb, hord b hbb]; exact a3
  · -- rows_ok
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hI.rows_ok r b
    refine ⟨?_, o2, o3, o4, o5, o6⟩
    by_cases hr : r = leaderOf N b'
    · subst hr
      have e : ((S.computeSync N b' M).rs (leaderOf N b')).locAt b =
          if b = b' then syncOrder M else (S.rs (leaderOf N b')).locAt b := by
        show ({ S.rs _ with locR := (if leaderOf N b' = leaderOf N b' then _ else _) } : RState).locAt b = _
        simp only [ite_true]; rw [RState.locAt_cons]
      rw [e]
      by_cases hbb : b = b'
      · subst hbb; simp only [ite_true]; exact hlocL
      · simp only [hbb, ite_false]; rw [hloc' _ b hbb]; exact o1
    · have e : ((S.computeSync N b' M).rs r).locAt b = (S.rs r).locAt b := by
        show ({ S.rs r with locR := (if r = leaderOf N b' then _ else _) } : RState).locAt b = _
        simp only [hr, ite_false]
      rw [e]
      by_cases hbb : b = b'
      · subst hbb; rw [hlocr r hr, ← o1, F0 r]
      · rw [hloc' r b hbb]; exact o1

theorem grow_depsIn (hI : S.PInv N fr) {S' : PState} (hc : S'.cmds = S.cmds) {r b : Nat}
    {t : List CmdId} (ht : S'.loc r b = S.loc r b ++ t) (y : CmdId) (hy : y ∈ S.loc r b) :
    depsIn (S'.seqOf (S'.loc r b)) y = depsIn (S.seqOf (S.loc r b)) y := by
  have e : S'.seqOf = S.seqOf := by funext l; unfold PState.seqOf; rw [hc]
  rw [e, ht, seqOf_append]
  exact depsIn_append_of_mem _ _ y (seqOf_mem_fst S _ y hy ((hI.loc_ok r b).2.1 y hy))

theorem grow_keyPrefix (hI : S.PInv N fr) {S' : PState} (hc : S'.cmds = S.cmds) {r b : Nat}
    {t : List CmdId} (ht : S'.loc r b = S.loc r b ++ t) (hB : S'.base b = S.base b) (y : CmdId)
    (hy : y ∈ S.loc r b) (hyB : y ∉ S.base b) : S'.keyPrefix r b y = S.keyPrefix r b y := by
  have hne : S.loc r b ≠ [] := fun h => by rw [h] at hy; simp at hy
  have hpre : S.base b <+: S.loc r b := by
    by_cases hb : b = 0
    · subst hb
      have : S.base 0 = [] := by
        unfold base; cases hs : S.sync 0 with
        | none => rfl
        | some M => have := (hI.sync_ok 0 M hs).1; omega
      rw [this]; exact List.nil_prefix
    · exact (((hI.loc_ok r b).2.2 hne).2.2 (by omega)).2
  obtain ⟨H, hH⟩ := hpre
  have hyH : y ∈ H := by rw [← hH] at hy; rcases List.mem_append.mp hy with h | h; exact absurd h hyB; exact h
  have e3 : S'.seqOf = S.seqOf := by funext l; unfold PState.seqOf; rw [hc]
  unfold keyPrefix
  rw [hc, hB, e3, ht, ← hH]
  simp only [List.append_assoc, List.drop_left]
  rw [seqOf_append]
  have := (before_append_of_mem (S.seqOf H) (S.seqOf t) y
    (seqOf_mem_fst S H y hyH ((hI.loc_ok r b).2.1 y hy))).1
  unfold before at this; rw [this]

/-- **Step MR2: replica `r` takes ballot `b'`'s `MSync`** (`handleSync`): its ballot and
`cballot` become `b'`, it is normal, its sequence of `b'` is the base (its handled list reset),
and it accepts every command of the base (its commits are then `PInv_commit` per command). -/
def takeSync (S : PState) (r b' : Nat) : PState :=
  { S with
    loc := fun r' b => if r' = r ∧ b = b' then S.base b' else S.loc r' b
    acc := fun r' b x => S.acc r' b x ∨ (r' = r ∧ b = b' ∧ x ∈ S.base b')
    rs := fun r' => { S.rs r' with
      ballot := if r' = r then b' else (S.rs r').ballot
      cballot := if r' = r then b' else (S.rs r').cballot
      normal := if r' = r then true else (S.rs r').normal
      locR := if r' = r then (b', S.base b') :: (S.rs r').locR else (S.rs r').locR
      accR := if r' = r then (S.base b').map (b', ·) ++ (S.rs r').accR else (S.rs r').accR } }

theorem PInv_takeSync (hI : S.PInv N fr) (r b' : Nat) (M : SyncMsg) (hr : r < N)
    (hM : S.sync b' = some M) (hbal : (S.rs r).ballot ≤ b')
    (hloc : S.loc r b' = [] ∨ S.loc r b' = S.base b') : (S.takeSync r b').PInv N fr := by
  have hb : 0 < b' := (hI.sync_ok b' M hM).1
  have hc : (S.takeSync r b').cmds = S.cmds := rfl
  have hB : ∀ b, (S.takeSync r b').base b = S.base b := fun b => rfl
  have hlocb : (S.takeSync r b').loc r b' = S.base b' := by
    show (if r = r ∧ b' = b' then _ else _) = _; simp
  have hlocn : ∀ r'' b, ¬ (r'' = r ∧ b = b') → (S.takeSync r b').loc r'' b = S.loc r'' b := by
    intro r'' b h; show (if _ then _ else _) = _; rw [if_neg h]
  have grow : ∀ r'' b, ∃ t, (S.takeSync r b').loc r'' b = S.loc r'' b ++ t := by
    intro r'' b
    by_cases h : r'' = r ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := h; rw [hlocb]
      rcases hloc with h | h
      · exact ⟨S.base b, by rw [h]; rfl⟩
      · exact ⟨[], by rw [h]; simp⟩
    · exact ⟨[], by rw [hlocn r'' b h]; simp⟩
  have mem : ∀ r'' b y, y ∈ S.loc r'' b → y ∈ (S.takeSync r b').loc r'' b := by
    intro r'' b y hy; obtain ⟨t, ht⟩ := grow r'' b; rw [ht]; exact List.mem_append_left _ hy
  have bal : ∀ r'', (S.rs r'').ballot ≤ ((S.takeSync r b').rs r'').ballot := by
    intro r''; show _ ≤ (if r'' = r then b' else (S.rs r'').ballot)
    by_cases h : r'' = r
    · subst h; simp [hbal]
    · simp [h]
  have hos : ∀ b y, y ∈ S.ord N b → depsIn ((S.takeSync r b').ordSeq N b) y = depsIn (S.ordSeq N b) y := by
    intro b y hy; obtain ⟨t, ht⟩ := grow (leaderOf N b) b
    exact grow_depsIn hI hc ht y hy
  have hseq : ∀ r'' b y, y ∈ S.loc r'' b →
      depsIn ((S.takeSync r b').seqOf ((S.takeSync r b').loc r'' b)) y = depsIn (S.seqOf (S.loc r'' b)) y := by
    intro r'' b y hy; obtain ⟨t, ht⟩ := grow r'' b; exact grow_depsIn hI hc ht y hy
  have hbaseord : S.base b' <+: S.ord N b' := (hI.sync_ok b' M hM).2.2.1
  have hordnd := (hI.loc_ok (leaderOf N b') b').1
  have hordreg := (hI.loc_ok (leaderOf N b') b').2.1
  have hrep_lt : ∀ b'' R, S.rep r b'' = some R → b'' ≤ b' := by
    intro b'' R h; have := (PState.repOk_parts (hI.rep_ok _ _ _ h)).1; omega
  refine ⟨fun r'' b => ?_, fun r'' => ?_, fun r'' b x hx => ?_, fun r'' b x D hx => ?_,
    fun r'' b x P hx => ?_, fun r'' b x hx => ?_, fun r'' b R hR => ?_, fun b M' hM' => ?_,
    fun r'' b => ?_, hI.G_ok⟩
  · -- loc_ok
    by_cases h : r'' = r ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := h
      rw [hlocb]
      refine ⟨hbaseord.sublist.nodup hordnd, fun y hy => hordreg y (hbaseord.subset hy), fun _ =>
        ⟨hr, show (if r'' = r'' then b else _) ≥ b by simp, fun _ =>
          ⟨by show S.sync _ ≠ none; rw [hM]; simp, by rw [hB]; exact List.prefix_refl _⟩⟩⟩
    · rw [hlocn r'' b h]
      obtain ⟨a1, a2, a3⟩ := hI.loc_ok r'' b
      exact ⟨a1, a2, fun hn => let x := a3 hn; ⟨x.1, Nat.le_trans x.2.1 (bal r''), x.2.2⟩⟩
  · -- rs_ok
    show (if r'' = r then b' else _) ≤ (if r'' = r then b' else _) ∧
      ((if r'' = r then true else _) = true → (if r'' = r then b' else _) = (if r'' = r then b' else _))
    by_cases h : r'' = r
    · simp [h]
    · simp only [h, ite_false]; exact hI.rs_ok r''
  · -- acc_ok
    rcases hx with hx | ⟨rfl, rfl, hxB⟩
    · obtain ⟨a1, a2, a3, a4, a5⟩ := hI.acc_ok r'' b x hx
      obtain ⟨t, ht⟩ := grow (leaderOf N b) b
      refine ⟨a1, mem _ _ _ a2, mem _ _ _ a3, Nat.le_trans a4 (bal r''), ?_⟩
      rw [hos b x a3]; intro hne d hd; exact (a5 hne d hd).imp Or.inl id
    · have hxo : x ∈ S.ord N b := hbaseord.subset hxB
      refine ⟨hr, by rw [hlocb]; exact hxB, mem _ _ _ hxo, show (if r'' = r'' then b else _) ≥ b by simp, ?_⟩
      rw [hos b x hxo]; intro _ d hd
      left; right
      exact ⟨rfl, rfl, base_deps S _ _ hbaseord hordnd hordreg hxB hd⟩
  · -- pre_ok
    obtain ⟨a1, a2, a3, a4, a5⟩ := hI.pre_ok r'' b x D hx
    exact ⟨a1, Nat.le_trans a2 (bal r''), mem _ _ _ a3, by rw [hseq r'' b x a3]; exact a4, a5⟩
  · -- path_ok
    obtain ⟨a1, a2, a3, a4, a5⟩ := hI.path_ok r'' b x P hx
    obtain ⟨t, ht⟩ := grow r'' b
    have e := grow_keyPrefix hI hc ht (hB b) x a1 a2
    exact ⟨mem _ _ _ a1, by rw [hB]; exact a2, a3, by rw [e]; exact a4, by rw [e]; exact a5⟩
  · -- com_ok
    obtain ⟨a1, a2, a3, a4⟩ := hI.com_ok r'' b x hx
    exact ⟨a1, Nat.le_trans a2 (bal r''), mem _ _ _ a3, a4.imp id (fun h => h.imp Or.inl id)⟩
  · -- rep_ok
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := PState.repOk_parts (hI.rep_ok r'' b R hR)
    have hnew : ∀ c', c' < b → ¬ (r'' = r ∧ c' = b') := by
      rintro c' hc' ⟨rfl, rfl⟩; have := hrep_lt _ _ hR; omega
    have hcl := hlocn r'' R.cbal (hnew _ p2)
    refine ⟨Nat.le_trans p1 (bal r''), p2, p3, fun c' y h1 h2 => ?_, fun y h => ?_, p6,
      fun hL y hy => ?_, by rw [hcl]; exact p8, fun e he => ?_⟩
    · obtain ⟨a, b2, c2, d⟩ := p4 c' y h1 h2
      refine ⟨fun h => h.elim a (fun ⟨h1', h2', _⟩ => hnew c' h2 ⟨h1', h2'⟩), b2, c2, ?_⟩
      rw [hlocn r'' c' (hnew c' h2)]; exact d
    · rcases h with (h | ⟨h1', h2', _⟩) | h
      · exact p5 y (Or.inl h)
      · exact absurd ⟨h1', h2'⟩ (hnew _ p2)
      · exact p5 y (Or.inr h)
    · apply p7 hL y
      by_cases hh : leaderOf N R.cbal = r ∧ R.cbal = b'
      · exact absurd (hL ▸ hh) (hnew _ p2)
      · rw [show (S.takeSync r b').ord N R.cbal = S.ord N R.cbal from hlocn _ _ hh] at hy; exact hy
    · obtain ⟨q1, q2, q3, q4, q5, q6⟩ := p9 e he
      refine ⟨q1, by rw [hcl]; exact q2, q3, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · obtain ⟨a, b2, c2⟩ := q4 h
        exact ⟨a.imp Or.inl id, mem _ _ _ b2, by rw [hos _ _ b2]; exact c2⟩
      · rcases q5 h with ⟨a, b2, c2⟩ | d
        · exact Or.inl ⟨a, mem _ _ _ b2, by rw [hos _ _ b2]; exact c2⟩
        · exact Or.inr d
      · intro d hd
        show d ∈ depsIn (S.seqOf ((S.takeSync r b').loc r'' R.cbal)) e.id
        rw [hcl]; exact q6 h d hd
  · -- sync_ok
    obtain ⟨a1, a2, a3, a4⟩ := hI.sync_ok b M' hM'
    obtain ⟨t, ht⟩ := grow (leaderOf N b) b
    refine ⟨a1, Nat.le_trans a2 (bal _), ?_, a4⟩
    rw [hB]; show S.base b <+: (S.takeSync r b').loc (leaderOf N b) b
    rw [ht]; exact a3.trans (List.prefix_append _ _)
  · -- rows_ok
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := hI.rows_ok r'' b
    by_cases hrr : r'' = r
    · subst hrr
      refine ⟨?_, fun x => ?_, o3, o4, o5, o6⟩
      · show (if r'' = r'' ∧ b = b' then _ else _) =
          ({ S.rs r'' with locR := (if r'' = r'' then (b', S.base b') :: (S.rs r'').locR else _) } : RState).locAt b
        simp only [true_and, ite_true]
        rw [RState.locAt_cons]
        by_cases hbb : b = b'
        · simp [hbb]
        · simp only [hbb, ite_false]; exact o1
      · show (S.acc r'' b x ∨ (r'' = r'' ∧ b = b' ∧ x ∈ S.base b')) ↔
          (b, x) ∈ (if r'' = r'' then (S.base b').map (b', ·) ++ (S.rs r'').accR else _)
        simp only [true_and, ite_true, List.mem_append, List.mem_map, Prod.mk.injEq, o2 x]
        constructor
        · rintro (h | ⟨rfl, h⟩)
          · exact Or.inr h
          · exact Or.inl ⟨x, h, rfl, rfl⟩
        · rintro (⟨x', h, rfl, rfl⟩ | h)
          · exact Or.inr ⟨rfl, h⟩
          · exact Or.inl h
    · refine ⟨?_, fun x => ?_, o3, o4, o5, o6⟩
      · rw [hlocn r'' b (fun h => hrr h.1)]
        show _ = ({ S.rs r'' with locR := (if r'' = r then _ else (S.rs r'').locR) } : RState).locAt b
        simp only [hrr, ite_false]; exact o1
      · show (S.acc r'' b x ∨ (r'' = r ∧ b = b' ∧ x ∈ S.base b')) ↔
          (b, x) ∈ (if r'' = r then _ else (S.rs r'').accR)
        simp only [hrr, false_and, or_false, ite_false]; exact o2 x

end PState

end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
