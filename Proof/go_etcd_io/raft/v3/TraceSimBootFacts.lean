/-
Lean-first (no Rocq counterpart). Trace-check's amendment A7 (Q29, 2026-11-11): what `NewTrace`
computes of a trace whose voters' bootstrap segments are raft's and complete (`BootSegs`, `BootDone`,
`TraceSimGhost.lean`). Raft-internal; its result is restated in `TraceSimEnd.lean`
(`newTrace_simInit`, which is `simInit C` since amendment A8).

- `bootstrapOf_eq`: `bootstrapOf`'s `find?`/`foldl` computation, for a server whose lines up to an
  index `c` are bootstrap-named and whose line at `c` (if any) is not: the flagged lines are its lines
  below `c`, the last one is their last;
- `newTrace_of_bootDone`: `newTrace` succeeds, its servers and initial servers are the voters', each
  voter's initial server the bootstrap state's (`simInit`), every other id's the server
  `newTraceWith` builds from the trace's first line (an `InitState`), `bootJunk`.
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSimBootSeg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

namespace TraceSim

/-! ## Generic list facts -/

theorem find?_of_first {α : Type _} (p : α → Bool) :
    ∀ (l : List α) (m : Nat) (hm : m < l.length), p l[m] = true → (∀ k (hk : k < m), p (l[k]'(by omega)) = false) →
      l.find? p = some l[m] := by
  intro l
  induction l with
  | nil => intro m hm; simp at hm
  | cons x l ih =>
    intro m hm hp hb
    cases m with
    | zero => simp at hp; simp [hp]
    | succ m =>
      have hx : p x = false := hb 0 (by omega)
      simp only [List.find?_cons, hx]
      exact ih m (by simp at hm; omega) hp (fun k hk => hb (k + 1) (by omega))

theorem foldl_lastIf {β : Type _} (q : Nat × β → Bool) :
    ∀ (l : List (Nat × β)) (a : Nat),
      l.foldl (fun (acc : Nat) p => if q p then p.1 else acc) a = (((l.filter q).getLast?).map Prod.fst).getD a := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons x l ih =>
    intro a
    rw [List.foldl_cons, ih]
    cases hq : q x
    · simp [hq]
    · cases hl : l.filter q with
      | nil => simp [hq, hl]
      | cons y ys =>
        simp only [List.filter_cons, hq, ↓reduceIte, hl]
        rw [List.getLast?_cons_cons]
        cases hg : (y :: ys).getLast? with
        | none => simp at hg
        | some z => simp



/-- The first index below `n` where `p` holds (`n` if none). -/
theorem find?_range_first (p : Nat → Bool) :
    ∀ n, ((List.range n).find? p).getD n ≤ n ∧ (((List.range n).find? p).getD n < n → p (((List.range n).find? p).getD n) = true) ∧
      ∀ k < ((List.range n).find? p).getD n, p k = false := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.find?_append]
    cases hf : (List.range n).find? p with
    | some c =>
      rw [hf] at ih
      simp only [Option.getD_some] at ih
      simp only [Option.some_or, Option.getD_some]
      obtain ⟨h1, h2, h3⟩ := ih
      have hc : c < n := by
        have := List.mem_range.1 (List.mem_of_find?_eq_some hf); exact this
      exact ⟨by omega, fun _ => h2 hc, h3⟩
    | none =>
      rw [hf] at ih
      simp only [Option.getD_none] at ih
      simp only [Option.none_or, List.find?_singleton]
      obtain ⟨-, -, h3⟩ := ih
      cases hp : p n
      · simp only [Bool.false_eq_true, ↓reduceIte, Option.getD_none]
        refine ⟨Nat.le_refl _, fun h => by omega, fun k hk => ?_⟩
        rcases Nat.lt_or_ge k n with h | h
        · exact h3 k h
        · have : k = n := by omega
          subst this; exact hp
      · simp only [↓reduceIte, Option.getD_some]
        exact ⟨by omega, fun _ => hp, h3⟩


theorem filterMap_congr' {α β : Type _} {f g : α → Option β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    rw [List.filterMap_cons, List.filterMap_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem mapM_ok_of {α β ε : Type} {f : α → Except ε β} (g : α → β) :
    ∀ (l : List α), (∀ x ∈ l, f x = .ok (g x)) → l.mapM f = .ok (l.map g) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    rw [List.mapM_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]
    rfl

theorem filterMapM_ok_of {α β ε : Type} {f : α → Except ε (Option β)} (g : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, f x = .ok (g x)) → l.filterMapM f = .ok (l.filterMap g) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    rw [List.filterMapM_cons, h a (by simp)]
    have := ih (fun x hx => h x (by simp [hx]))
    cases hg : g a with
    | none => simp only [bind, Except.bind, hg, List.filterMap_cons]; exact this
    | some b =>
      simp only [bind, Except.bind, hg, List.filterMap_cons, this]
      rfl

theorem find?_key {β : Type _} (g : Nat → β) (i : Nat) :
    ∀ (l : List Nat), (l.map (fun i => (i, g i))).find? (fun p => p.1 == i) = if i ∈ l then some (i, g i) else none := by
  intro l
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.find?_cons]
    by_cases hx : x = i
    · subst hx; simp
    · have : (x == i) = false := by simpa using hx
      simp only [this, ih]
      by_cases hi : i ∈ l
      · simp [hi]
      · simp [hi, Ne.symm hx]

/-! ## The segments as index sets -/

theorem takeWhile_eq_filter_lt (b : Nat → Bool) (c : Nat) :
    ∀ (S : List Nat), S.Pairwise (· < ·) → (∀ x ∈ S, x < c → b x = true) →
      (∀ x ∈ S, c ≤ x → ∃ y ∈ S, c ≤ y ∧ y ≤ x ∧ b y = false) →
      S.takeWhile b = S.filter (fun x => decide (x < c)) := by
  intro S
  induction S with
  | nil => intro _ _ _; rfl
  | cons x S ih =>
    intro hs hb hc
    have hs' := List.pairwise_cons.1 hs
    by_cases hx : x < c
    · simp only [List.takeWhile_cons, hb x (by simp) hx, ↓reduceIte, List.filter_cons, hx, decide_true]
      rw [ih hs'.2 (fun y hy => hb y (by simp [hy])) ?_]
      intro y hy hcy
      obtain ⟨z, hz, hcz, hzy, hbz⟩ := hc y (by simp [hy]) hcy
      rcases List.mem_cons.1 hz with rfl | hz
      · omega
      · exact ⟨z, hz, hcz, hzy, hbz⟩
    · obtain ⟨z, hz, hcz, hzx, hbz⟩ := hc x (by simp) (by omega)
      have hzx' : z = x := by
        rcases List.mem_cons.1 hz with rfl | hz
        · rfl
        · have := hs'.1 z hz; omega
      subst hzx'
      simp only [List.takeWhile_cons, hbz, Bool.false_eq_true, ↓reduceIte]
      symm
      rw [List.filter_eq_nil_iff]
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · simpa using hx
      · have := hs'.1 y hy; simp; omega

theorem filter_eq_range {α : Type _} (L : List α) (e0 : α) (p : α → Bool) :
    L.filter p = ((List.range L.length).filter (fun k => p (L.getD k e0))).map (fun k => L.getD k e0) := by
  have hL : L = (List.range L.length).map (fun k => L.getD k e0) := by
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  conv => lhs; rw [hL]
  rw [List.filter_map]
  rfl

/-- **A voter's segment by its indices** below the first index `c` of its lines not bootstrap-named. -/
theorem bootSeg_eq_range [GooseExts] (L : List TraceEv) (e0 : TraceEv) (j : w64) (c : Nat) (hcn : c ≤ L.length)
    (hB : ∀ k < c, (L.getD k e0).nid = decStr j → Etcdraft.isBootstrapName (gsStr (L.getD k e0).name) = true)
    (hc : c < L.length → (L.getD c e0).nid = decStr j ∧
      Etcdraft.isBootstrapName (gsStr (L.getD c e0).name) = false) :
    bootSeg L j = ((List.range L.length).filter
      (fun k => decide ((L.getD k e0).nid = decStr j ∧ k < c))).map (fun k => L.getD k e0) := by
  unfold bootSeg
  rw [filter_eq_range L e0, List.takeWhile_map]
  congr 1
  rw [takeWhile_eq_filter_lt _ c, List.filter_filter]
  · apply List.filter_congr; intro k _; simp [Bool.and_comm]
  · exact List.pairwise_lt_range.filter _
  · intro x hx hxc
    exact hB x hxc (by simpa using (List.mem_filter.1 hx).2)
  · intro x hx hcx
    have hxn := List.mem_range.1 (List.mem_filter.1 hx).1
    obtain ⟨h1, h2⟩ := hc (by omega)
    exact ⟨c, List.mem_filter.2 ⟨List.mem_range.2 (by omega), by simpa using h1⟩, Nat.le_refl _, hcx, h2⟩

/-! ## `bootstrapOf` -/

section boot
variable (ls : List Etcdraft.Line) (i : Etcdraft.ID)

/-- **`bootstrapOf` of a server whose lines are bootstrap-named below `c`** (and its line at `c`, if
any, is not), its first line `f < c`: the flagged lines are its lines below `c`, the last one their
last. -/
theorem bootstrapOf_eq (c f : Nat) (hcn : c ≤ ls.length)
    (hB : ∀ k < c, (ls.getD k default).nid = i → Etcdraft.isBootstrapName (ls.getD k default).ev.name = true)
    (hc : c < ls.length → (ls.getD c default).nid = i ∧ Etcdraft.isBootstrapName (ls.getD c default).ev.name = false)
    (hfc : f < c) (hPf : (ls.getD f default).nid = i) (hmin : ∀ k < f, (ls.getD k default).nid ≠ i) :
    Etcdraft.bootstrapOf ls i =
      ((List.range ls.length).map (fun k => decide ((ls.getD k default).nid = i ∧ k < c)),
       ((((List.range ls.length).filter (fun k => decide ((ls.getD k default).nid = i ∧ k < c))).getLast?).map
         (· + 1)).getD 0) := by
  unfold Etcdraft.bootstrapOf
  simp only
  generalize hI : (List.range ls.length).map (fun k => (k + 1, ls.getD k default)) = I
  have hIl : I.length = ls.length := by rw [← hI]; simp
  have hIk : ∀ k (hk : k < I.length), I[k] = (k + 1, ls.getD k default) := by
    intro k hk; subst hI; simp only [List.getElem_map, List.getElem_range]
  have hfirst : I.find? (fun (p : Nat × Etcdraft.Line) => p.2.nid == i && Etcdraft.isBootstrapName p.2.ev.name) =
      some (f + 1, ls.getD f default) := by
    rw [← hIk f (by omega)]
    apply find?_of_first
    · rw [hIk]
      simp only [beq_iff_eq, Bool.and_eq_true]
      exact ⟨hPf, hB f hfc hPf⟩
    · intro k hk; rw [hIk]
      have := hmin k hk
      generalize ls.getD k default = x at this ⊢
      simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
      exact .inl this
  have hnon : I.find? (fun (p : Nat × Etcdraft.Line) => p.2.nid == i && !Etcdraft.isBootstrapName p.2.ev.name) =
      if c < ls.length then some (c + 1, ls.getD c default) else none := by
    by_cases hcl : c < ls.length
    · rw [if_pos hcl, ← hIk c (by omega)]
      apply find?_of_first
      · rw [hIk]
        obtain ⟨h1, h2⟩ := hc hcl
        simp only [beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true']
        exact ⟨h1, h2⟩
      · intro k hk; rw [hIk k (by omega)]
        have := hB k hk
        generalize ls.getD k default = x at this ⊢
        by_cases hn : x.nid = i
        · simp only [Bool.and_eq_false_iff, Bool.not_eq_false', beq_eq_false_iff_ne]
          exact .inr (this hn)
        · simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
          exact .inl hn
    · rw [if_neg hcl, List.find?_eq_none]
      intro p hp
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hp
      rw [hIk]
      have := hB k (by omega)
      generalize ls.getD k default = x at this ⊢
      by_cases hn : x.nid = i
      · simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', not_and, Bool.not_eq_false]
        intro _; exact this hn
      · simp only [Bool.and_eq_true, beq_iff_eq, not_and]
        intro h; exact absurd h hn
  rw [hfirst, hnon]
  simp only [Option.map_some, Option.getD_some]
  have hmax : max (f + 1) 1 = f + 1 := by omega
  simp only [hmax]
  -- the upper bound of the flagged lines: `c` (or the end)
  generalize hU : (if (Option.map Prod.fst (if c < ls.length then some (c + 1, ls.getD c default) else none)).getD 0 != 0
      then (Option.map Prod.fst (if c < ls.length then some (c + 1, ls.getD c default) else none)).getD 0 - 1
      else ls.length) = U
  have hUc : ∀ k < ls.length, (k + 1 ≤ U ↔ k < c) := by
    intro k hk
    rw [← hU]
    by_cases hcl : c < ls.length
    · simp only [hcl, ↓reduceIte, Option.map_some, Option.getD_some]
      have : (c + 1 != 0) = true := by simp
      simp only [this, ↓reduceIte]; omega
    · simp only [hcl, ↓reduceIte, Option.map_none, Option.getD_none]
      have : ((0 : Nat) != 0) = false := by simp
      simp only [this, Bool.false_eq_true, ↓reduceIte]; omega
  have hisB : ∀ k (hk : k < ls.length),
      (decide (f + 1 ≤ k + 1) && decide (k + 1 ≤ U) && (ls.getD k default).nid == i) =
        decide ((ls.getD k default).nid = i ∧ k < c) := by
    intro k hk
    have hu := hUc k hk
    have hm := hmin k
    generalize ls.getD k default = x at hm ⊢
    by_cases hn : x.nid = i
    · have hfk : f ≤ k := by
        rcases Nat.lt_or_ge k f with h | h
        · exact absurd hn (hm h)
        · exact h
      have h1 : decide (f + 1 ≤ k + 1) = true := by simp; omega
      rw [h1, Bool.true_and]
      have h2 : (x.nid == i) = true := by simpa using hn
      rw [h2, Bool.and_true]
      simp only [Bool.true_and, decide_eq_decide, hn, true_and]
      exact hu
    · have : (x.nid == i) = false := by simpa using hn
      rw [this, Bool.and_false]
      symm; simp only [decide_eq_false_iff_not, not_and]; intro h; exact absurd h hn
  refine Prod.ext ?_ ?_
  · show I.map _ = _
    rw [← hI, List.map_map]
    apply List.map_congr_left
    intro k hk
    exact hisB k (List.mem_range.1 hk)
  · show List.foldl _ 0 I = _
    rw [foldl_lastIf, ← hI, List.filter_map, List.getLast?_map, Option.map_map]
    have hf : List.filter ((fun (p : Nat × Etcdraft.Line) => decide (f + 1 ≤ p.1) && decide (p.1 ≤ U) && p.2.nid == i) ∘
        fun k => (k + 1, ls.getD k default)) (List.range ls.length) =
        (List.range ls.length).filter (fun k => decide ((ls.getD k default).nid = i ∧ k < c)) :=
      List.filter_congr (fun k hk => hisB k (List.mem_range.1 hk))
    rw [hf]
    rfl
end boot

/-! ## A voter's bootstrap lines in the parsed trace -/

section voter
variable [GooseExts]

/-- The parsed lines, index by index. -/
theorem parseLines_getD (L : List TraceEv) (e0 : TraceEv) (lines : List Etcdraft.Line)
    (hl : parseLines (L.map evConv) = .ok lines) :
    lines.length = L.length ∧ ∀ k < L.length,
      Etcdraft.parseLine 0 (evConv (L.getD k e0)) = .ok (lines.getD k default) := by
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  refine ⟨hlen, fun k hk => ?_⟩
  unfold parseLines at hl
  obtain ⟨y, hy, hfy⟩ := mapM_ok_get _ _ _ hl k (by simp; exact hk)
  simp only [List.getElem_zip, List.getElem_range, List.getElem_map] at hfy
  rw [List.getElem?_eq_getElem (by omega)] at hy
  cases hy
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega)]
  exact parseLine_idx k 0 _ _ hfy

/-- **A voter's bootstrap lines as `bootstrapOf` computes them** (its segment complete): `T` the
indices of its segment's events, `bootstrapOf` flags exactly them, the last one is the segment's
last. -/
theorem voter_bootstrapOf (C : List w64) (L : List TraceEv) (e0 : TraceEv) (lines : List Etcdraft.Line)
    (j : w64) (_hj : j ∈ C)
    (hlen : lines.length = L.length)
    (hpl : ∀ k < L.length, Etcdraft.parseLine 0 (evConv (L.getD k e0)) = .ok (lines.getD k default))
    (hseg : BootSegs C L) (hdone : BootDone C L j) :
    ∃ T : List Nat, T.length = C.length + 4 ∧ (∀ k ∈ T, k < L.length) ∧
      bootSeg L j = T.map (fun k => L.getD k e0) ∧
      (List.range lines.length).filter (fun k => ((Etcdraft.bootstrapOf lines (idAbs j)).1).getD k false) = T ∧
      (Etcdraft.bootstrapOf lines (idAbs j)).2 = T.getLastD 0 + 1 := by
  classical
  -- line `k`'s node and name, from its event
  have hnid : ∀ k < L.length, ((lines.getD k default).nid = idAbs j ↔ (L.getD k e0).nid = decStr j) := by
    intro k hk
    have hmem : L.getD k e0 ∈ L := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem _
    obtain ⟨w, -, hw⟩ := hseg.1 _ hmem
    rw [parseLine_nid_decStr _ w _ hw (hpl k hk), hw]
    exact ⟨fun h => by rw [idAbs_inj.1 h], fun h => by rw [decStr_inj h]⟩
  have hname : ∀ k < L.length, (lines.getD k default).ev.name = gsStr (L.getD k e0).name := by
    intro k hk; rw [parseLine_ev' _ _ _ (hpl k hk)]; rfl
  let P : Nat → Prop := fun k => (L.getD k e0).nid = decStr j
  let B : Nat → Bool := fun k => Etcdraft.isBootstrapName (gsStr (L.getD k e0).name)
  have hcF := find?_range_first (fun k => decide (P k ∧ B k = false)) L.length
  generalize ((List.range L.length).find? (fun k => decide (P k ∧ B k = false))).getD L.length = c at hcF
  obtain ⟨hcn, hcc', hcmin⟩ := hcF
  have hBc : ∀ k < c, P k → B k = true := by
    intro k hk hP
    have := hcmin k hk
    cases hb : B k
    · simp [hP, hb] at this
    · rfl
  have hcc : c < L.length → P c ∧ B c = false := by
    intro h; simpa using hcc' h
  have hseq := bootSeg_eq_range L e0 j c hcn hBc hcc
  generalize hT : (List.range L.length).filter (fun k => decide ((L.getD k e0).nid = decStr j ∧ k < c)) = T at hseq
  have hTl : T.length = C.length + 4 := by
    have := hdone; unfold BootDone at this; rw [hseq, List.length_map] at this; exact this
  have hTmem : ∀ k, k ∈ T ↔ k < L.length ∧ P k ∧ k < c := by
    intro k; rw [← hT, List.mem_filter, List.mem_range]; simp [P]
  -- its first line
  have hfex : ∃ k, k < L.length ∧ P k := by
    have h0 : 0 < T.length := by omega
    obtain ⟨h1, h2, -⟩ := (hTmem T[0]).1 (List.getElem_mem h0)
    exact ⟨_, h1, h2⟩
  have hfF := find?_range_first (fun k => decide (P k)) L.length
  generalize ((List.range L.length).find? (fun k => decide (P k))).getD L.length = f at hfF
  obtain ⟨hfn, hff, hfmin'⟩ := hfF
  have hfmin : ∀ k < f, ¬ P k := by
    intro k hk hP; have := hfmin' k hk; simp [hP] at this
  have hfl : f < L.length := by
    obtain ⟨k, hk, hP⟩ := hfex
    rcases Nat.lt_or_ge k f with h | h
    · exact absurd hP (hfmin k h)
    · omega
  have hfspec : f < L.length ∧ P f := ⟨hfl, by simpa using hff hfl⟩
  have hfc : f < c := by
    have h0 : 0 < T.length := by omega
    obtain ⟨h1, h2, h3⟩ := (hTmem T[0]).1 (List.getElem_mem h0)
    rcases Nat.lt_or_ge T[0] f with h | h
    · exact absurd h2 (hfmin _ h)
    · omega
  have hbo := bootstrapOf_eq lines (idAbs j) c f (by omega)
    (fun k hk hn => by
      rw [hname k (by omega)]; exact hBc k hk ((hnid k (by omega)).1 hn))
    (fun h => by
      obtain ⟨h1, h2⟩ := hcc (by omega)
      exact ⟨(hnid c (by omega)).2 h1, by rw [hname c (by omega)]; exact h2⟩)
    hfc ((hnid f hfspec.1).2 hfspec.2) (fun k hk hn => hfmin k hk ((hnid k (by omega)).1 hn))
  have hTl' : (List.range lines.length).filter (fun k => decide ((lines.getD k default).nid = idAbs j ∧ k < c)) = T := by
    rw [← hT, hlen]
    apply List.filter_congr
    intro k hk
    have hk' := List.mem_range.1 hk
    simp only [decide_eq_decide]
    rw [hnid k hk']
  refine ⟨T, hTl, fun k hk => ((hTmem k).1 hk).1, hseq, ?_, ?_⟩
  · rw [hbo, ← hTl']
    apply List.filter_congr
    intro k hk
    have hk' := List.mem_range.1 hk
    simp only
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk']
    rfl
  · rw [hbo, hTl']
    cases hTe : T.getLast? with
    | none => simp at hTe; subst hTe; simp at hTl
    | some x =>
      rw [List.getLastD_eq_getLast?, hTe]
      rfl

theorem mem_confAbs_inv' (C : List w64) (x : Etcdraft.ID) (h : x ∈ confAbs C) : ∃ w ∈ C, idAbs w = x := by
  unfold confAbs at h
  rw [setIds_mk_mem] at h
  exact List.mem_map.1 h

theorem parseLine_role (k : Nat) (ev : Etcdraft.Event) (ln : Etcdraft.Line)
    (h : Etcdraft.parseLine k ev = .ok ln) : ln.role = ev.role := by
  unfold Etcdraft.parseLine at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (first | (split at h) | (cases h; done) | (injection h with h; subst h; rfl))

theorem parseLine_vote (k : Nat) (ev : Etcdraft.Event) (ln : Etcdraft.Line)
    (h : Etcdraft.parseLine k ev = .ok ln) : Etcdraft.parseID ev.state.vote = some ln.vote := by
  unfold Etcdraft.parseLine at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (first | (split at h) | (cases h; done) | (injection h with h; subst h; assumption))

theorem toSet_decStr' (ns : List w64) :
    Etcdraft.toSet ((ns.map decStr).map gsStr) = some (Etcdraft.SetIds.mk (ns.map idAbs)) := by
  rw [List.map_map]; exact toSet_decStr ns

theorem setIds_mk_perm_take (ns xs : List w64) (h : ns.Perm xs) :
    Etcdraft.SetIds.mk (ns.map idAbs) = confAbs xs := by
  unfold confAbs
  apply setIds_mk_eq
  intro x
  simp only [List.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, h.mem_iff.1 hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, h.mem_iff.2 hw, rfl⟩

theorem evConv_newconf (x : TraceEv) (c : TraceCC) (h : x.propCC = some c) :
    ((evConv x).prop.bind Etcdraft.EventProps.cc).bind Etcdraft.EventConfChange.newconf =
      if c.newconf.isEmpty then none else some (c.newconf.map gsStr) := by
  simp only [evConv, h, Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
    Option.map_some, ccConv]

/-- The bootstrap events before `Bootstrap`'s configuration changes carry no new configuration. -/
theorem bootEv_cc_none (C : List w64) (w : w64) (m : Nat) (x : TraceEv) (hm : m < 4) (h : BootEvAt C w m x) :
    gsStr x.name ≠ "ApplyConfChange" ∨
      ((evConv x).prop.bind Etcdraft.EventProps.cc).bind Etcdraft.EventConfChange.newconf = none := by
  match m, hm with
  | 0, _ => left; rw [h.2.1]; decide
  | 1, _ => right; rw [evConv_newconf x _ h.2.2.2]; rfl
  | 2, _ => left; rw [h.2.1]; decide
  | 3, _ => left; rw [h.2.1]; decide

/-- `Bootstrap`'s `q`-th (from 0) configuration change: the first `q + 1` voters. -/
theorem bootEv_cc_some (C : List w64) (w : w64) (q : Nat) (x : TraceEv) (h : BootEvAt C w (q + 4) x) :
    gsStr x.name = "ApplyConfChange" ∧ ∃ ns : List w64, ns.Perm (C.take (q + 1)) ∧
      ((evConv x).prop.bind Etcdraft.EventProps.cc).bind Etcdraft.EventConfChange.newconf =
        some ((ns.map decStr).map gsStr) := by
  obtain ⟨hq, -, hn, -, -, -, -, -, ns, hns, hcc⟩ := h
  refine ⟨hn, ns, hns, ?_⟩
  rw [evConv_newconf x _ hcc]
  have hne : ns ≠ [] := by
    intro h0; subst h0
    have := hns.length_eq; simp at this; omega
  simp only [List.isEmpty_map]
  cases ns with
  | nil => exact absurd rfl hne
  | cons a ns => rfl

/-- A line's bootstrap configuration as `NewTrace`'s `BootstrapEntryConf` collects it. -/
def bootCfgOf (ln : Etcdraft.Line) : Option Etcdraft.SetIds :=
  if (ln.ev.name != "ApplyConfChange") = true then none
  else match (ln.ev.prop.bind Etcdraft.EventProps.cc).bind Etcdraft.EventConfChange.newconf with
    | none => none
    | some nc => Etcdraft.toSet nc

theorem bootCfgOf_at (C : List w64) (w : w64) (m : Nat) (x : TraceEv) (ln : Etcdraft.Line)
    (h : BootEvAt C w m x) (hp : Etcdraft.parseLine 0 (evConv x) = .ok ln) :
    bootCfgOf ln = (if m < 4 then none else some (confAbs (C.take (m - 3)))) ∧
    (ln.ev.name = "ApplyConfChange" → ∀ nc,
      (ln.ev.prop.bind Etcdraft.EventProps.cc).bind Etcdraft.EventConfChange.newconf = some nc →
      ∃ c, Etcdraft.toSet nc = some c) := by
  have hev := parseLine_ev' _ _ _ hp
  unfold bootCfgOf
  rw [hev]
  by_cases hm : m < 4
  · rw [if_pos hm]
    rcases bootEv_cc_none C w m x hm h with hn | hn
    · have : ((evConv x).name != "ApplyConfChange") = true := by
        show (gsStr x.name != "ApplyConfChange") = true; simpa using hn
      refine ⟨by simp only [this, ↓reduceIte], fun h' => absurd h' hn⟩
    · refine ⟨?_, fun _ nc hnc => by rw [hn] at hnc; cases hnc⟩
      split
      · rfl
      · rw [hn]
  · rw [if_neg hm]
    obtain ⟨q, rfl⟩ : ∃ q, m = q + 4 := ⟨m - 4, by omega⟩
    obtain ⟨hn, ns, hns, hnc⟩ := bootEv_cc_some C w q x h
    have hn' : ((evConv x).name != "ApplyConfChange") = false := by
      show (gsStr x.name != "ApplyConfChange") = false; simpa using hn
    have hts := toSet_decStr' ns
    rw [setIds_mk_perm_take ns _ hns] at hts
    refine ⟨?_, fun _ nc hnc' => by rw [hnc] at hnc'; cases hnc'; exact ⟨_, hts⟩⟩
    simp only [hn', Bool.false_eq_true, ↓reduceIte, hnc, hts]
    congr 3

/-- **What `NewTrace` computes of a trace whose voters' bootstrap segments are raft's and complete.** -/
theorem newTrace_of_bootDone (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hC0 : C ≠ [])
    (hCl : C.length < 2 ^ 40) (hrun : SimRun C L σ) (hev : SimEvents C.length L) (hseg : BootSegs C L)
    (hdone : ∀ i ∈ C, BootDone C L i) :
    ∃ t, Etcdraft.newTrace (L.map evConv) = .ok t ∧ t.server = confAbs C ∧ t.initSrv = confAbs C ∧
      t.init = { simInit C with s := fun i => if i ∈ confAbs C then (simInit C).s i else
        let v : Etcdraft.Server :=
          { currentTerm := 0, state := Etcdraft.follower, votedFor := Etcdraft.nil, lead := Etcdraft.nil,
            log := [], commitIndex := 0, votesResponded := [], votesGranted := [], matchIndex := fun _ => 0,
            pendingConfChangeIndex := 0, config := { incoming := [], outgoing := [], learners := [] },
            durable := default }
        { v with durable := Etcdraft.durableOf v } } := by
  obtain ⟨j0, hj0⟩ : ∃ j, j ∈ C := ⟨C.head hC0, List.head_mem hC0⟩
  have hL0 : L ≠ [] := by
    intro h; have := hdone j0 hj0; subst h; simp [BootDone, bootSeg] at this
  obtain ⟨e0, -⟩ : ∃ e, e ∈ L := List.exists_mem_of_ne_nil L hL0
  obtain ⟨lines, hl⟩ : ∃ lines, parseLines (L.map evConv) = .ok lines := by
    rcases hrun with ⟨h, -⟩ | ⟨lines, ts, hl, -⟩
    · exact absurd h hL0
    · exact ⟨lines, hl⟩
  obtain ⟨hlen, hpl⟩ := parseLines_getD L e0 lines hl
  -- every event is a voter's, not a `ChangeConf`
  have hnidL : ∀ k < L.length, ∃ w ∈ C, (L.getD k e0).nid = decStr w ∧ (lines.getD k default).nid = idAbs w := by
    intro k hk
    have hmem : L.getD k e0 ∈ L := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem _
    obtain ⟨w, hw, hwn⟩ := hseg.1 _ hmem
    exact ⟨w, hw, hwn, parseLine_nid_decStr _ w _ hwn (hpl k hk)⟩
  have hnoCC : ∀ ln ∈ lines, ln.ev.name ≠ "ChangeConf" := by
    intro ln hln
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hln
    have hk' : k < L.length := by omega
    have hg : lines[k] = lines.getD k default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
    rw [hg, parseLine_ev' _ _ _ (hpl k hk')]
    have hsc := hev.2.1 k hk'
    have hLk : L[k] = L.getD k e0 := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']; rfl
    rw [hLk] at hsc
    show gsStr (L.getD k e0).name ≠ "ChangeConf"
    rcases hsc with h | ⟨h, -⟩
    · exact h.1
    · intro hc; rw [hc] at h; exact absurd h (by decide)
  have hadd : lines.mapM Etcdraft.addedServer = .ok (lines.map (fun _ => (none : Option Etcdraft.ID))) := by
    apply mapM_ok_of
    intro ln hln
    unfold Etcdraft.addedServer
    have : (ln.ev.name != "ChangeConf") = true := by simpa using hnoCC ln hln
    simp only [this, ↓reduceIte]; rfl
  have hsrv : Etcdraft.SetIds.mk (lines.map Etcdraft.Line.nid ++
      (lines.map (fun _ => (none : Option Etcdraft.ID))).filterMap id) = confAbs C := by
    have : (lines.map (fun _ => (none : Option Etcdraft.ID))).filterMap id = [] := by simp
    rw [this, List.append_nil]
    unfold confAbs
    apply setIds_mk_eq
    intro x
    constructor
    · intro hx
      obtain ⟨ln, hln, rfl⟩ := List.mem_map.1 hx
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hln
      obtain ⟨w, hw, -, hwl⟩ := hnidL k (by omega)
      have hg : lines[k] = lines.getD k default := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
      rw [hg, hwl]; exact List.mem_map_of_mem hw
    · intro hx
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      have hd := hdone w hw
      unfold BootDone at hd
      have hne : bootSeg L w ≠ [] := by intro h; rw [h] at hd; simp at hd
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
      have hxF := List.mem_filter.1 (List.takeWhile_subset _ hx)
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hxF.1
      have hLk : L[k] = L.getD k e0 := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
      obtain ⟨w', -, hw'n, hw'l⟩ := hnidL k hk
      rw [← hLk] at hw'n
      have : w' = w := decStr_inj (by rw [← hw'n]; simpa using hxF.2)
      subst this
      exact List.mem_map.2 ⟨lines.getD k default, by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _, hw'l⟩
  have hE : (List.map evConv L).isEmpty = false := by simpa using hL0
  have hl' := hl
  unfold parseLines at hl'
  unfold Etcdraft.newTrace Etcdraft.newTraceWith
  simp only [bind, Except.bind, pure, Except.pure, hE, Bool.false_eq_true, ↓reduceIte, hl', hadd, hsrv]
  -- each voter's bootstrap lines
  have hvoter := fun w (hw : w ∈ C) => voter_bootstrapOf C L e0 lines w hw hlen hpl hseg (hdone w hw)
  -- each voter's last bootstrap line: `Bootstrap`'s last configuration change
  have hlast : ∀ w ∈ C, (Etcdraft.bootstrapOf lines (idAbs w)).2 ≠ 0 ∧ ∃ x,
      BootEvAt C w (C.length - 1 + 4) x ∧
      Etcdraft.parseLine 0 (evConv x) = .ok (lines.getD ((Etcdraft.bootstrapOf lines (idAbs w)).2 - 1) default) := by
    intro w hw
    obtain ⟨T, hTl, hTlt, hseqT, -, hlT⟩ := hvoter w hw
    have hk : T.getLastD 0 = T[C.length + 3]'(by omega) := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
      simp [hTl]
    refine ⟨by rw [hlT]; omega, (bootSeg L w)[C.length + 3]'(by rw [hseqT]; simp [hTl]), ?_, ?_⟩
    · have hb := hseg.2 w hw (C.length + 3) (by rw [hseqT]; simp [hTl])
      obtain ⟨x, hx⟩ : ∃ x, (bootSeg L w)[C.length + 3]'(by rw [hseqT]; simp [hTl]) = x := ⟨_, rfl⟩
      rw [hx] at hb ⊢
      have he : C.length + 3 = C.length - 1 + 4 := by
        have := List.length_pos_iff.2 hC0; omega
      rw [he] at hb
      exact hb
    · rw [hlT, Nat.add_sub_cancel, hk]
      have hx : (bootSeg L w)[C.length + 3]'(by rw [hseqT]; simp [hTl]) = L.getD (T[C.length + 3]'(by omega)) e0 := by
        simp only [hseqT, List.getElem_map]
      rw [hx]
      exact hpl _ (hTlt _ (List.getElem_mem _))
  simp only [find?_key]
  have hz : List.find? (fun p => p.snd.snd == 0)
      (List.map (fun i => (i, Etcdraft.bootstrapOf lines i)) (confAbs C)) = none := by
    rw [List.find?_eq_none]
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
    obtain ⟨w, hw, rfl⟩ := mem_confAbs_inv' C i hi
    simpa using (hlast w hw).1
  obtain ⟨w0, hw0, hL0n, hl0n⟩ := hnidL 0 (List.length_pos_iff.2 hL0)
  have h0mem : (lines.getD 0 default).nid ∈ confAbs C := by rw [hl0n]; exact (mem_confAbs C w0).2 hw0
  -- each server's last bootstrap line: its configuration the voters'
  have hcfg : ∀ i ∈ confAbs C,
      (lines.getD ((Etcdraft.bootstrapOf lines i).2 - 1) default).ev.name = "ApplyConfChange" ∧
      ∃ nc, (((lines.getD ((Etcdraft.bootstrapOf lines i).2 - 1) default).ev.prop.bind Etcdraft.EventProps.cc).bind
        Etcdraft.EventConfChange.newconf) = some nc ∧ Etcdraft.toSet nc = some (confAbs C) := by
    intro i hi
    obtain ⟨w, hw, rfl⟩ := mem_confAbs_inv' C i hi
    obtain ⟨-, x, hx, hpx⟩ := hlast w hw
    rw [parseLine_ev' _ _ _ hpx]
    obtain ⟨hn, ns, hns, hnc⟩ := bootEv_cc_some C w _ x hx
    refine ⟨hn, _, hnc, ?_⟩
    rw [toSet_decStr', setIds_mk_perm_take ns C]
    have : C.length - 1 + 1 = C.length := by have := List.length_pos_iff.2 hC0; omega
    rw [this, List.take_length] at hns
    exact hns
  have hsub : Etcdraft.SetIds.subset (confAbs C) (confAbs C) = true := by
    unfold Etcdraft.SetIds.subset; simp
  obtain ⟨hn0, nc0, hnc0, hts0⟩ := hcfg _ h0mem
  simp only [hz, h0mem, ↓reduceIte, Option.map_some, Option.getD_some, hn0, hnc0, hts0, beq_self_eq_true,
    hsub, Bool.not_true, Bool.false_eq_true]
  rw [mapM_ok_of (fun i => (i, confAbs C)) (confAbs C)]
  rotate_left
  · intro i hi
    obtain ⟨hn, nc, hnc, hts⟩ := hcfg i hi
    simp only [hi, ↓reduceIte, Option.map_some, Option.getD_some, hn, hnc, hts, beq_self_eq_true]
  simp only
  rw [mapM_ok_of (fun i => (i, (List.range C.length).map (fun q => confAbs (C.take (q + 1))))) (confAbs C)]
  rotate_left
  · intro i hi
    simp only [hi, ↓reduceIte, Option.map_some, Option.getD_some]
    obtain ⟨w, hw, rfl⟩ := mem_confAbs_inv' C i hi
    obtain ⟨T, hTl, hTlt, hseqT, hflt, -⟩ := hvoter w hw
    rw [hflt]
    -- each segment line's configuration
    have hat : ∀ m (hm : m < T.length), BootEvAt C w m (L.getD (T[m]) e0) ∧
        Etcdraft.parseLine 0 (evConv (L.getD (T[m]) e0)) = .ok (lines.getD (T[m]) default) := by
      intro m hm
      have hb := hseg.2 w hw m (by rw [hseqT]; simpa using hm)
      have hx : (bootSeg L w)[m]'(by rw [hseqT]; simpa using hm) = L.getD (T[m]) e0 := by
        simp only [hseqT, List.getElem_map]
      rw [hx] at hb
      exact ⟨hb, hpl _ (hTlt _ (List.getElem_mem _))⟩
    rw [filterMapM_ok_of (fun k => bootCfgOf (lines.getD k default)) T]
    rotate_left
    · intro k hk
      obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hk
      obtain ⟨hb, hp⟩ := hat m hm
      obtain ⟨-, hok⟩ := bootCfgOf_at C w m _ _ hb hp
      simp only [bootCfgOf]
      by_cases hn : ((lines.getD T[m] default).ev.name != "ApplyConfChange") = true
      · simp only [hn, ↓reduceIte]
      · simp only [hn, Bool.false_eq_true, ↓reduceIte]
        have hn' : (lines.getD T[m] default).ev.name = "ApplyConfChange" := by simpa using hn
        cases hnc : ((lines.getD T[m] default).ev.prop.bind Etcdraft.EventProps.cc).bind
            Etcdraft.EventConfChange.newconf with
        | none => rfl
        | some nc =>
          obtain ⟨c, hc⟩ := hok hn' nc hnc
          simp only [hc]
    simp only
    congr 2
    -- the configurations, in order: the first `q + 1` voters
    have hTr : T = (List.range T.length).map (fun m => T.getD m 0) := by
      apply List.ext_getElem (by simp)
      intro k h1 h2
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
    rw [hTr, List.filterMap_map, hTl, Nat.add_comm, List.range_add, List.filterMap_append]
    have hg : ∀ m (hm : m < C.length + 4), bootCfgOf (lines.getD (T.getD m 0) default) =
        (if m < 4 then none else some (confAbs (C.take (m - 3)))) := by
      intro m hm
      have hgd : T.getD m 0 = T[m]'(by omega) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      obtain ⟨hb, hp⟩ := hat m (by omega)
      rw [hgd]
      exact (bootCfgOf_at C w m _ _ hb hp).1
    have h1 : (List.range 4).filterMap ((fun k => bootCfgOf (lines.getD k default)) ∘ fun m => T.getD m 0) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro m hm
      have hm' := List.mem_range.1 hm
      simp only [Function.comp_apply]
      rw [hg m (by omega), if_pos hm']
    have h2 : ((List.range C.length).map (fun q => 4 + q)).filterMap
        ((fun k => bootCfgOf (lines.getD k default)) ∘ fun m => T.getD m 0) =
        (List.range C.length).map (fun q => confAbs (C.take (q + 1))) := by
      rw [List.filterMap_map, ← List.filterMap_eq_map']
      apply filterMap_congr'
      intro q hq
      have hq' := List.mem_range.1 hq
      simp only [Function.comp_apply]
      rw [hg (4 + q) (by omega), if_neg (by omega)]
      congr 3; omega
    rw [h1, h2, List.nil_append]
  simp only
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  have gInt_nat : ∀ n : Nat, n < 2 ^ 40 → gInt (W64 n) = (n : Int) := by
    intro n hn; unfold gInt; word
  simp only [find?_key]
  unfold simInit
  congr 1
  funext i
  by_cases hi : i ∈ confAbs C
  · simp only [hi, ↓reduceIte, Option.map_some, Option.getD_some]
    obtain ⟨w, hw, rfl⟩ := mem_confAbs_inv' C i hi
    obtain ⟨-, x, hx, hpx⟩ := hlast w hw
    have hev := parseLine_ev' _ _ _ hpx
    have hrole := parseLine_role _ _ _ hpx
    have hvote := parseLine_vote _ _ _ hpx
    generalize lines.getD ((Etcdraft.bootstrapOf lines (idAbs w)).2 - 1) default = lb at hev hrole hvote
    obtain ⟨-, -, -, hterm, hv, hcm, hls, hro, -⟩ := hx
    rw [hrole]
    have hvote' : lb.vote = Etcdraft.nil := by
      simp only [evConv, hv, parseID_decStr] at hvote
      exact (Option.some.inj hvote).symm
    have ht : (evConv x).state.term = 1 := by
      show gInt x.term = 1; rw [hterm]; exact gInt_nat 1 (by decide)
    have hc : (evConv x).state.commit = C.length := by
      show gInt x.commit = _; rw [hcm]; exact gInt_nat _ hCl
    have hlg : (evConv x).log.toNat = C.length := by
      show (gInt x.logSize).toNat = _; rw [hls, gInt_nat _ hCl]; simp
    have hr : (evConv x).role = Etcdraft.follower := by
      show gsStr x.role = _; rw [hro]; rfl
    rw [hev, ht, hc, hlg, hr, hvote']
    have hlog : ∀ k ∈ List.range C.length,
        ((List.map (fun q => confAbs (List.take (q + 1) C)) (List.range C.length)).getD k (confAbs C)) =
          confAbs (C.take (k + 1)) := by
      intro k hk
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (List.mem_range.1 hk)]
      rfl
    rw [List.map_congr_left (fun k hk => by rw [hlog k hk])]
  · simp only [hi, ↓reduceIte, Option.map_none, Option.getD_none, Nat.zero_sub]
    -- the trace's first line: its node's `InitState`
    have hpos0 : BootEvAt C w0 0 (L.getD 0 e0) := by
      have hd := hdone w0 hw0
      unfold BootDone at hd
      have hb := hseg.2 w0 hw0 0 (by omega)
      obtain ⟨a, L', hLa⟩ : ∃ a L', L = a :: L' := by
        cases L with
        | nil => exact absurd rfl hL0
        | cons a L' => exact ⟨a, L', rfl⟩
      subst hLa
      have ha : a.nid = decStr w0 := by simpa using hL0n
      have hseg0 : bootSeg (a :: L') w0 = (a :: L'.filter (fun x => decide (x.nid = decStr w0))).takeWhile
          (fun x => Etcdraft.isBootstrapName (gsStr x.name)) := by
        unfold bootSeg; simp [List.filter_cons, ha]
      have hfst : (bootSeg (a :: L') w0)[0]'(by omega) = a := by
        cases hba : Etcdraft.isBootstrapName (gsStr a.name)
        · exfalso; rw [hseg0] at hd; simp [List.takeWhile_cons, hba] at hd
        · simp only [hseg0, List.takeWhile_cons, hba, ↓reduceIte, List.getElem_cons_zero]
      rw [hfst] at hb
      exact hb
    have hp0 := hpl 0 (List.length_pos_iff.2 hL0)
    have hev := parseLine_ev' _ _ _ hp0
    have hrole := parseLine_role _ _ _ hp0
    have hvote := parseLine_vote _ _ _ hp0
    generalize lines.getD 0 default = lb at hev hrole hvote
    obtain ⟨-, -, hterm, hv, hcm, hls, hro⟩ := hpos0
    rw [hrole]
    have hvote' : lb.vote = Etcdraft.nil := by
      simp only [evConv, hv, parseID_decStr] at hvote
      exact (Option.some.inj hvote).symm
    have ht : (evConv (L.getD 0 e0)).state.term = 0 := by
      show gInt (L.getD 0 e0).term = 0; rw [hterm]; exact gInt_nat 0 (by decide)
    have hc : (evConv (L.getD 0 e0)).state.commit = 0 := by
      show gInt (L.getD 0 e0).commit = 0; rw [hcm]; exact gInt_nat 0 (by decide)
    have hlg : (evConv (L.getD 0 e0)).log.toNat = 0 := by
      show (gInt (L.getD 0 e0).logSize).toNat = 0
      have h0 : gInt (W64 0) = 0 := by unfold gInt; word
      rw [hls, h0]; rfl
    have hr : (evConv (L.getD 0 e0)).role = Etcdraft.follower := by
      show gsStr (L.getD 0 e0).role = _; rw [hro]; rfl
    rw [hev, ht, hc, hlg, hr, hvote']
    rfl

end voter

end TraceSim

end EtcdGrove
end Perennial
