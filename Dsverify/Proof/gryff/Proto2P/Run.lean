/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto2P/Run.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit I (stage 2 proofs): pure facts about one replica's runs and the global runs, used by the
invariant's laws (`Proto2/*`).

* `runFrom` over an appended list; `stOf`, `outsP`, `streamOf` after one more step;
* global runs (`GRun`) split at an append; a run's configuration holds each replica's state after
  its projection, and the messages in flight to `q` are, as a multiset, those sent to `q` minus
  those `q` consumed (`grun_init_acc`).

The lemmas are stated over a generic `kahn.Net` where they can be (`Fin gNet.n` is `Fin 3` only up
to unfolding `gNet`, which `rw` does not see through) and instantiated at `gNet` with `exact`.
-/
module

public import Dsverify.Proof.gryff.Proto2.InvDefs
public import Dsverify.Proof.gryff.Pure.Totality

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.p2

open model kahn pure

instance inv2St_inhabited : Inhabited Inv2St :=
  ⟨⟨fun _ => [], [], ∅, ∅, ∅, ∅, W64 0, [], ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅⟩⟩

/-! ## Sums over the processes -/

/-- The sum of `f` over the processes. -/
def sumN (N : Net) (f : Fin N.n → Nat) : Nat := ((List.finRange N.n).map f).sum

theorem sumL_add {α : Type} (f g : α → Nat) :
    ∀ L : List α, (L.map (fun k => f k + g k)).sum = (L.map f).sum + (L.map g).sum
  | [] => rfl
  | x :: L => by simp only [List.map_cons, List.sum_cons, sumL_add f g L]; omega

theorem sumL_zero {α : Type} : ∀ L : List α, (L.map (fun _ => 0)).sum = 0
  | [] => rfl
  | _ :: L => by simp only [List.map_cons, List.sum_cons, sumL_zero L]

theorem sumL_ite {α : Type} [DecidableEq α] (i : α) (a : Nat) :
    ∀ L : List α, L.Nodup → i ∈ L → (L.map (fun k => if k = i then a else 0)).sum = a
  | [], _, h => absurd h List.not_mem_nil
  | x :: L, hn, h => by
    rw [List.nodup_cons] at hn
    simp only [List.map_cons, List.sum_cons]
    by_cases hx : x = i
    · subst hx
      have : (L.map (fun k => if k = x then a else 0)).sum = 0 := by
        have : ∀ k ∈ L, (if k = x then a else 0) = 0 := by
          intro k hk; have : k ≠ x := fun e => hn.1 (e ▸ hk); exact ite_eq_right_iff.2 (fun h => absurd h this)
        rw [List.map_congr_left this]; exact sumL_zero L
      rw [this]; simp
    · simp only [hx, ↓reduceIte, Nat.zero_add]
      exact sumL_ite i a L hn.2 (by rcases List.mem_cons.1 h with h | h; exact absurd h.symm hx; exact h)

theorem sumL_le {α : Type} {f g : α → Nat} (h : ∀ k, f k ≤ g k) :
    ∀ L : List α, (L.map f).sum ≤ (L.map g).sum
  | [] => Nat.le_refl _
  | x :: L => by simp only [List.map_cons, List.sum_cons]; have := h x; have := sumL_le h L; omega

theorem sumN_add (N : Net) (f g : Fin N.n → Nat) :
    sumN N (fun k => f k + g k) = sumN N f + sumN N g := sumL_add f g _

theorem sumN_ite (N : Net) (i : Fin N.n) (a : Nat) :
    sumN N (fun k => if k = i then a else 0) = a :=
  sumL_ite i a _ (List.nodup_finRange _) (List.mem_finRange i)

theorem sumN_le {N : Net} {f g : Fin N.n → Nat} (h : ∀ k, f k ≤ g k) : sumN N f ≤ sumN N g :=
  sumL_le h _

theorem sumN_congr {N : Net} {f g : Fin N.n → Nat} (h : ∀ k, f k = g k) : sumN N f = sumN N g := by
  unfold sumN; congr 1; exact List.map_congr_left (fun k _ => h k)

/-! ## One process's runs (generic) -/

theorem runFrom_append (N : Net) (i : Fin N.n) :
    ∀ (s : N.S) (es1 es2 : List N.E), runFrom N i s (es1 ++ es2) =
      (runFrom N i s es1).bind
        (fun r => (runFrom N i r.1 es2).map (fun r' => (r'.1, r.2 ++ r'.2)))
  | s, [], es2 => by
    simp only [List.nil_append, runFrom, Option.bind_some, List.nil_append]
    cases runFrom N i s es2 <;> rfl
  | s, e :: es1, es2 => by
    simp only [List.cons_append, runFrom]
    cases N.step i s e with
    | none => rfl
    | some p =>
      obtain ⟨s', o⟩ := p
      simp only
      rw [runFrom_append N i s' es1 es2]
      cases runFrom N i s' es1 with
      | none => rfl
      | some r =>
        simp only [Option.bind_some, Option.map_some, Option.map_map]
        cases runFrom N i r.1 es2 <;> simp [Function.comp_def]

theorem runP_snoc_gen (N : Net) (k : Fin N.n) {t : List N.E} {s s' : N.S}
    {o o' : List (kahn.Out N.n N.M N.X)} {e : N.E}
    (h : runP N k t = some (s, o)) (hs : N.step k s e = some (s', o')) :
    runP N k (t ++ [e]) = some (s', o ++ o') := by
  unfold runP at *
  rw [runFrom_append N k (N.init k) t [e], h]
  simp [runFrom, hs]

theorem runP_prefix_gen (N : Net) (k : Fin N.n) {t u : List N.E} {s : N.S}
    {o : List (kahn.Out N.n N.M N.X)}
    (h : runP N k (t ++ u) = some (s, o)) :
    ∃ s1 o1, runP N k t = some (s1, o1) ∧ o1 <+: o := by
  unfold runP at *
  rw [runFrom_append N k (N.init k) t u] at h
  cases h1 : runFrom N k (N.init k) t with
  | none => rw [h1] at h; cases h
  | some r =>
    rw [h1] at h
    simp only [Option.bind_some] at h
    cases h2 : runFrom N k r.1 u with
    | none => rw [h2] at h; cases h
    | some r' =>
      rw [h2] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨r.1, r.2, rfl, ⟨r'.2, h.2⟩⟩

theorem sentTo_append_gen (N : Net) (q : Fin N.n) (o o' : List (kahn.Out N.n N.M N.X)) :
    sentTo N q (o ++ o') = sentTo N q o ++ sentTo N q o' := by
  unfold sentTo; exact List.filterMap_append

theorem proj_append_gen (N : Net) (l l' : List (Fin N.n × N.E)) (r : Fin N.n) :
    proj l r ++ proj l' r = proj (l ++ l') r := by
  unfold proj; simp [List.filter_append]

theorem proj_cons_gen (N : Net) (i r : Fin N.n) (e : N.E) (l : List (Fin N.n × N.E)) :
    proj ((i, e) :: l) r = (if r = i then [e] else []) ++ proj l r := by
  unfold proj
  by_cases hk : r = i
  · subst hk; simp
  · have : ¬ (i = r) := fun e => hk e.symm
    simp [hk, this]

theorem proj_single_gen (N : Net) (i r : Fin N.n) (e : N.E) :
    proj [(i, e)] r = if r = i then [e] else [] := by
  rw [proj_cons_gen]; simp [proj]

theorem recvd_append_gen (N : Net) (es es' : List N.E) :
    recvd N (es ++ es') = recvd N es ++ recvd N es' := by
  unfold recvd; exact List.filterMap_append

/-! ## The model's instances -/

theorem gStep_ok {k : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (hs : stepR k s e = .ok (s', o)) : gNet.step k s e = some (s', o) := by
  show (stepR k s e).toOption = _
  rw [hs]; rfl

theorem runP_snoc {k : Fin 3} {t : List Ev} {s s' : RState} {o o' : List Out} {e : Ev}
    (h : runP gNet k t = some (s, o)) (hs : stepR k s e = .ok (s', o')) :
    runP gNet k (t ++ [e]) = some (s', o ++ o') :=
  runP_snoc_gen gNet k h (gStep_ok hs)

theorem runP_prefix {k : Fin 3} {t u : List Ev} {s : RState} {o : List Out}
    (h : runP gNet k (t ++ u) = some (s, o)) :
    ∃ s1 o1, runP gNet k t = some (s1, o1) ∧ o1 <+: o :=
  runP_prefix_gen gNet k h

theorem stOf_of_runP {k : Fin 3} {t : List Ev} {s : RState} {o : List Out}
    (h : runP gNet k t = some (s, o)) : stOf k t = s := by
  unfold stOf; rw [h]

theorem outsP_of_runP {k : Fin 3} {t : List Ev} {s : RState} {o : List Out}
    (h : runP gNet k t = some (s, o)) : outsP k t = o := by
  unfold outsP; rw [h]; rfl

theorem sentTo_append (q : Fin 3) (o o' : List Out) :
    sentToR q (o ++ o') = sentToR q o ++ sentToR q o' :=
  sentTo_append_gen gNet q o o'

theorem sentTo_prefix (q : Fin 3) {o o' : List Out} (h : o <+: o') :
    sentToR q o <+: sentToR q o' := by
  obtain ⟨r, rfl⟩ := h
  rw [sentTo_append]; exact List.prefix_append _ _

/-- One step of a replica whose trace runs: its state, outputs and streams after it. -/
theorem step_snoc {k : Fin 3} {t : List Ev} {s s' : RState} {o outs : List Out} {e : Ev}
    (h : runP gNet k t = some (s, o)) (hs : stepR k (stOf k t) e = .ok (s', outs)) :
    runP gNet k (t ++ [e]) = some (s', o ++ outs) ∧ stOf k (t ++ [e]) = s' ∧
      outsP k (t ++ [e]) = outsP k t ++ outs ∧
      ∀ q, streamOf k q (t ++ [e]) = streamOf k q t ++ sentToR q outs := by
  rw [stOf_of_runP h] at hs
  have h' := runP_snoc h hs
  refine ⟨h', stOf_of_runP h', ?_, ?_⟩
  · rw [outsP_of_runP h', outsP_of_runP h]
  · intro q; unfold streamOf; rw [outsP_of_runP h', outsP_of_runP h, sentTo_append]

/-- A prefix of a running trace runs, and its streams are prefixes. -/
theorem streamOf_prefix {k : Fin 3} {t t' : List Ev} {s : RState} {o : List Out}
    (h : runP gNet k t' = some (s, o)) (hp : t <+: t') (q : Fin 3) :
    streamOf k q t <+: streamOf k q t' := by
  obtain ⟨u, rfl⟩ := hp
  obtain ⟨s1, o1, h1, ho⟩ := runP_prefix h
  unfold streamOf; rw [outsP_of_runP h1, outsP_of_runP h]
  exact sentTo_prefix q ho

theorem runP_prefix' {k : Fin 3} {t t' : List Ev} {s : RState} {o : List Out}
    (h : runP gNet k t' = some (s, o)) (hp : t <+: t') :
    ∃ s1 o1, runP gNet k t = some (s1, o1) := by
  obtain ⟨u, rfl⟩ := hp
  obtain ⟨s1, o1, h1, -⟩ := runP_prefix h
  exact ⟨s1, o1, h1⟩

theorem proj_append (l l' : List Label) (r : Fin 3) :
    projR (l ++ l') r = projR l r ++ projR l' r :=
  (proj_append_gen gNet l l' r).symm

theorem proj_snoc (l : List Label) (k r : Fin 3) (e : Ev) :
    projR (l ++ [(k, e)]) r = projR l r ++ (if r = k then [e] else []) := by
  rw [proj_append]
  congr 1
  exact proj_single_gen gNet k r e

/-! ## Global runs -/

theorem grun_append {N : Net} {c c' : Cfg N} :
    ∀ {l1 l2 : List (Fin N.n × N.E)}, GRun c (l1 ++ l2) c' ↔ ∃ c1, GRun c l1 c1 ∧ GRun c1 l2 c'
  | [], l2 => by
    simp only [List.nil_append]
    constructor
    · intro h; exact ⟨c, .nil c, h⟩
    · rintro ⟨c1, h1, h2⟩; cases h1; exact h2
  | x :: l1, l2 => by
    constructor
    · intro h
      cases h with
      | cons hs hr =>
        obtain ⟨c1, h1, h2⟩ := (grun_append (l1 := l1) (l2 := l2)).1 hr
        exact ⟨c1, .cons hs h1, h2⟩
    · rintro ⟨c1, h1, h2⟩
      cases h1 with
      | cons hs hr =>
        exact .cons hs ((grun_append (l1 := l1) (l2 := l2)).2 ⟨c1, hr, h2⟩)

theorem grun_snoc {N : Net} {c c1 c' : Cfg N} {l : List (Fin N.n × N.E)} {i : Fin N.n} {e : N.E}
    {x : List N.X} (h : GRun c l c1) (hs : GStep c1 i e c' x) : GRun c (l ++ [(i, e)]) c' :=
  grun_append.2 ⟨c1, h, .cons hs (.nil c')⟩

theorem count_consume {M : Type} [DecidableEq M] (m : M) (r : Option M) (l : List M)
    (h : ∀ m', r = some m' → m' ∈ l) :
    (consume r l).count m + ((r.map (fun x => [x])).getD []).count m = l.count m := by
  cases r with
  | none => simp [consume]
  | some m' =>
    simp only [consume, Option.map_some, Option.getD_some]
    have hm := h m' rfl
    rw [List.count_erase]
    by_cases e : m' = m
    · subst e
      have : 0 < l.count m' := List.count_pos_iff.2 hm
      simp; omega
    · have : (m' == m) = false := by simp [e]
      simp [this, List.count_singleton]

theorem recvd_single_gen (N : Net) (e : N.E) (m : N.M) :
    (recvd N [e]).count m = ((N.recv e).map (fun x => [x]) |>.getD []).count m := by
  unfold recvd
  rw [List.filterMap_cons, List.filterMap_nil]
  cases N.recv e <;> rfl

/-- **The accounting of a run** (relative to its start): each process's run from its state over
its projection, and the in-flight messages (counted). -/
theorem grun_acc {N : Net} {c c' : Cfg N} {l : List (Fin N.n × N.E)} (h : GRun c l c') :
    ∃ O : Fin N.n → List (kahn.Out N.n N.M N.X),
      (∀ k, runFrom N k (c.st k) (proj l k) = some (c'.st k, O k)) ∧
      ∀ q m, (c'.inflight q).count m + (recvd N (proj l q)).count m =
        (c.inflight q).count m + sumN N (fun k => (sentTo N q (O k)).count m) := by
  induction h with
  | nil c =>
    refine ⟨fun _ => [], fun k => ?_, fun q m => ?_⟩
    · simp [proj, runFrom]
    · simp only [proj, recvd, sumN, sentTo, List.filter_nil, List.map_nil, List.filterMap_nil,
        List.count_nil, Nat.add_zero]
      rw [sumL_zero]; rfl
  | @cons c c1 c' i e x l hs hr ih =>
    obtain ⟨O1, hO1, hc1⟩ := ih
    obtain ⟨s', o, hstep, hrecv, -, hst, hinf⟩ := hs
    refine ⟨fun k => (if k = i then o else []) ++ O1 k, fun k => ?_, fun q m => ?_⟩
    · rw [proj_cons_gen]
      by_cases hk : k = i
      · subst hk
        simp only [↓reduceIte, List.singleton_append, runFrom]
        rw [hstep]
        simp only
        have := hO1 k
        rw [hst] at this; simp only [↓reduceIte] at this
        rw [this]; rfl
      · simp only [hk, ↓reduceIte, List.nil_append]
        have := hO1 k
        rw [hst] at this; simp only [hk, ↓reduceIte] at this
        exact this
    · have := hc1 q m
      rw [hinf] at this
      simp only at this
      rw [proj_cons_gen, recvd_append_gen, List.count_append]
      rw [List.count_append] at this
      simp only
      have hs3 : sumN N (fun k => (sentTo N q ((if k = i then o else []) ++ O1 k)).count m) =
          (sentTo N q o).count m + sumN N (fun k => (sentTo N q (O1 k)).count m) := by
        rw [← sumN_ite N i ((sentTo N q o).count m), ← sumN_add]
        apply sumN_congr; intro k
        rw [sentTo_append_gen, List.count_append]
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk, sentTo]
      rw [hs3]
      by_cases hq : q = i
      · subst hq
        simp only [↓reduceIte] at this ⊢
        have hcons := count_consume m (N.recv e) (c.inflight q) (fun m' h => hrecv m' h)
        rw [recvd_single_gen]
        omega
      · simp only [hq, ↓reduceIte] at this ⊢
        simp only [recvd, List.filterMap_nil, List.count_nil] at this ⊢
        omega

/-- From the initial configuration: each replica's state and outputs after its projection, and
the in-flight messages to `q`: sent to `q` minus consumed by `q`. -/
theorem grun_init_acc {c : Cfg gNet} {l : List Label} (h : GRun (Cfg.init gNet) l c) :
    (∀ k : Fin 3, runP gNet k (projR l k) = some (c.st k, outsP k (projR l k))) ∧
      ∀ (q : Fin 3) m, (c.inflight q).count m + (recvd gNet (projR l q)).count m =
        sumN gNet (fun k => (streamOf k q (projR l k)).count m) := by
  obtain ⟨O, hO, hc⟩ := grun_acc h
  have hr : ∀ k : Fin 3, runP gNet k (projR l k) = some (c.st k, O k) := fun k => hO k
  refine ⟨fun k => by rw [hr k, outsP_of_runP (hr k)]; exact rfl, fun q m => ?_⟩
  rw [hc q m]
  have : ((Cfg.init gNet).inflight q).count m = 0 := rfl
  rw [this, Nat.zero_add]
  apply sumN_congr; intro k
  show _ = (sentToR q (outsP k (projR l k))).count m
  rw [outsP_of_runP (hr k)]; rfl

/-- A message counted more often among the sends to `q` than among `q`'s receipts is in
flight. -/
theorem inflight_of_count {c : Cfg gNet} {l : List Label} (h : GRun (Cfg.init gNet) l c)
    {q : Fin 3} {m : Msg}
    (hlt : (recvd gNet (projR l q)).count m <
      sumN gNet (fun k => (streamOf k q (projR l k)).count m)) :
    m ∈ c.inflight q := by
  have h1 := (grun_init_acc h).2 q m
  have h2 : List.count (α := gNet.M) m (recvd gNet (projR l q)) <
      sumN gNet (fun k => List.count (α := gNet.M) m (streamOf k q (projR l k))) := hlt
  have h3 : 0 < List.count (α := gNet.M) m (c.inflight q) := by omega
  exact (List.count_pos_iff (α := gNet.M)).1 h3

end Perennial.gryff.p2
