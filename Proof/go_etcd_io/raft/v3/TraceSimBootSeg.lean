/-
Lean-first (no Rocq counterpart). Trace-check's amendment A7 (Q29, 2026-11-11): how a line moves the
voters' bootstrap segments (`BootSegs`, a `simInv` clause, `TraceSimGhost.lean`). A line not
bootstrap-named, or of a node whose segment is over (`booted`), leaves every segment as it is
(`bootSegs_snoc_other`); a bootstrap line of an unbooted node extends its own, by the event raft
logs next (`BootNext`, the bootstrap law's premise: `bootSegs_snoc_boot`). Raft-internal.
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSimRun
public import Proof.go_etcd_io.raft.v3.TraceSimStr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

namespace TraceSim

variable [GooseExts]

theorem takeWhile_snoc {α : Type _} (p : α → Bool) :
    ∀ (l : List α) (a : α), (l ++ [a]).takeWhile p = if l.all p then l ++ [a].takeWhile p else l.takeWhile p := by
  intro l a
  induction l with
  | nil => simp
  | cons x l ih =>
    by_cases hx : p x = true
    · simp only [List.cons_append, List.takeWhile_cons, hx, ↓reduceIte, ih, List.all_cons, Bool.true_and]
      split <;> rfl
    · simp only [Bool.not_eq_true] at hx
      simp [hx]

theorem takeWhile_all {α : Type _} (p : α → Bool) (l : List α) (h : l.all p = true) : l.takeWhile p = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [h.1, ih h.2]

/-- Another node's line leaves a segment as it is. -/
theorem bootSeg_snoc_ne (L : List TraceEv) (e : TraceEv) (i : w64) (h : e.nid ≠ decStr i) :
    bootSeg (L ++ [e]) i = bootSeg L i := by
  unfold bootSeg
  simp [List.filter_append, h]

/-- A node's line not bootstrap-named, or after one, leaves its segment as it is. -/
theorem bootSeg_snoc_stop (L : List TraceEv) (e : TraceEv) (i : w64)
    (h : Etcdraft.isBootstrapName (gsStr e.name) = false ∨
      ∃ x ∈ L, x.nid = decStr i ∧ Etcdraft.isBootstrapName (gsStr x.name) = false) :
    bootSeg (L ++ [e]) i = bootSeg L i := by
  by_cases hn : e.nid = decStr i
  · unfold bootSeg
    rw [List.filter_append]
    simp only [List.filter_cons, List.filter_nil, hn, decide_true, ↓reduceIte]
    rw [takeWhile_snoc]
    rcases h with h | ⟨x, hx, hxn, hxb⟩
    · split
      · rename_i hall
        simp [h, takeWhile_all _ _ hall]
      · rfl
    · have : (L.filter (fun x => decide (x.nid = decStr i))).all
          (fun x => Etcdraft.isBootstrapName (gsStr x.name)) = false := by
        rw [List.all_eq_false]
        exact ⟨x, List.mem_filter.2 ⟨hx, by simp [hxn]⟩, by simp [hxb]⟩
      simp [this]
  · exact bootSeg_snoc_ne L e i hn

/-- A line of an unbooted node, bootstrap-named, extends its segment by it. -/
theorem bootSeg_snoc_boot (L : List TraceEv) (e : TraceEv) (i : w64) (hn : e.nid = decStr i)
    (hall : ∀ x ∈ L, x.nid = decStr i → Etcdraft.isBootstrapName (gsStr x.name) = true)
    (hb : Etcdraft.isBootstrapName (gsStr e.name) = true) :
    bootSeg L i = L.filter (fun x => decide (x.nid = decStr i)) ∧
    bootSeg (L ++ [e]) i = L.filter (fun x => decide (x.nid = decStr i)) ++ [e] := by
  have ha : (L.filter (fun x => decide (x.nid = decStr i))).all
      (fun x => Etcdraft.isBootstrapName (gsStr x.name)) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨hx, hxn⟩ := List.mem_filter.1 hx
    exact hall x hx (by simpa using hxn)
  refine ⟨takeWhile_all _ _ ha, ?_⟩
  unfold bootSeg
  rw [List.filter_append]
  simp only [List.filter_cons, List.filter_nil, hn, decide_true, ↓reduceIte]
  rw [takeWhile_snoc, ha]
  simp [hb]

/-- The node a parsed line names, by its id's string. -/
theorem parseLine_nid' (k : Nat) (ev : Etcdraft.Event) (ln : Etcdraft.Line)
    (h : Etcdraft.parseLine k ev = .ok ln) : Etcdraft.parseID ev.nid = some ln.nid := by
  unfold Etcdraft.parseLine at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (first | (split at h) | (cases h; done) | (injection h with h; subst h; assumption))

/-- A parsed line's event. -/
theorem parseLine_ev' (k : Nat) (ev : Etcdraft.Event) (ln : Etcdraft.Line)
    (h : Etcdraft.parseLine k ev = .ok ln) : ln.ev = ev := by
  unfold Etcdraft.parseLine at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (first | (split at h) | (cases h; done) | (injection h with h; subst h; rfl))

/-- A voter's event parses to a line of that voter. -/
theorem parseLine_nid_decStr (x : TraceEv) (j : w64) (ln : Etcdraft.Line) (hx : x.nid = decStr j)
    (hp : Etcdraft.parseLine 0 (evConv x) = .ok ln) : ln.nid = idAbs j := by
  have h := parseLine_nid' 0 _ _ hp
  simp only [evConv, hx, parseID_decStr] at h
  exact (Option.some.inj h).symm

/-- **A booted node, by its id's string**: it has an event not bootstrap-named. -/
theorem booted_str (C : List w64) (L : List TraceEv) (id : w64) (hs : BootSegs C L)
    (hb : booted L (idAbs id)) :
    ∃ x ∈ L, x.nid = decStr id ∧ Etcdraft.isBootstrapName (gsStr x.name) = false := by
  obtain ⟨x, hx, ln, hp, hn, hbn⟩ := hb
  obtain ⟨j, -, hj⟩ := hs.1 x hx
  have := parseLine_nid_decStr x j ln hj hp
  rw [hn] at this
  have hji : j = id := (idAbs_inj.1 this).symm
  subst hji
  refine ⟨x, hx, hj, ?_⟩
  rw [parseLine_ev' _ _ _ hp] at hbn
  exact hbn

/-- **A line not bootstrap-named, or of a booted node, keeps the segments.** -/
theorem bootSegs_snoc_other (C : List w64) (L : List TraceEv) (e : TraceEv) (id : w64) (hC : id ∈ C)
    (hnid : e.nid = decStr id) (hs : BootSegs C L)
    (h : Etcdraft.isBootstrapName (gsStr e.name) = false ∨ booted L (idAbs id)) :
    BootSegs C (L ++ [e]) := by
  refine ⟨forall_mem_snoc L e hs.1 ⟨id, hC, hnid⟩, ?_⟩
  intro i hi
  have heq : bootSeg (L ++ [e]) i = bootSeg L i := by
    by_cases hii : i = id
    · subst hii
      apply bootSeg_snoc_stop
      rcases h with h | h
      · exact .inl h
      · exact .inr (booted_str C L i hs h)
    · exact bootSeg_snoc_ne L e i (by rw [hnid]; exact fun h => hii (decStr_inj h).symm)
  rw [heq]
  exact hs.2 i hi

/-- A run's events parse (each to a line). -/
theorem simRun_parse (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ) :
    ∀ x ∈ L, ∃ ln, Etcdraft.parseLine 0 (evConv x) = .ok ln := by
  intro x hx
  rcases hrun with ⟨rfl, -⟩ | ⟨lines, ts, hl, -⟩
  · simp at hx
  · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    unfold parseLines at hl
    obtain ⟨y, -, hfy⟩ := mapM_ok_get _ _ _ hl k (by simp; exact hk)
    simp only [List.getElem_zip, List.getElem_range, List.getElem_map] at hfy
    exact ⟨y, parseLine_idx k 0 _ _ hfy⟩

/-- **A bootstrap line of an unbooted node extends its segment** by raft's next bootstrap event. -/
theorem bootSegs_snoc_boot (C : List w64) (L : List TraceEv) (e : TraceEv) (id : w64) (o : Option TraceEv)
    (hC : id ∈ C) (hnid : e.nid = decStr id) (hs : BootSegs C L)
    (hparse : ∀ x ∈ L, ∃ ln, Etcdraft.parseLine 0 (evConv x) = .ok ln)
    (hun : ¬ booted L (idAbs id)) (hb : Etcdraft.isBootstrapName (gsStr e.name) = true)
    (hlast : LastOf L (decStr id) o) (hnext : BootNext C id o e) :
    BootSegs C (L ++ [e]) := by
  have hall : ∀ x ∈ L, x.nid = decStr id → Etcdraft.isBootstrapName (gsStr x.name) = true := by
    intro x hx hxn
    cases hxb : Etcdraft.isBootstrapName (gsStr x.name)
    · exfalso; apply hun
      obtain ⟨ln, hp⟩ := hparse x hx
      exact ⟨x, hx, ln, hp, parseLine_nid_decStr x id ln hxn hp, by rw [parseLine_ev' _ _ _ hp]; exact hxb⟩
    · rfl
  obtain ⟨hs0, hs1⟩ := bootSeg_snoc_boot L e id hnid hall hb
  refine ⟨forall_mem_snoc L e hs.1 ⟨id, hC, hnid⟩, ?_⟩
  intro i hi
  by_cases hii : i = id
  · subst hii
    rw [hs1]
    have hF := hs.2 i hi
    rw [hs0] at hF
    generalize hFd : L.filter (fun x => decide (x.nid = decStr i)) = F at hF
    -- the new event's position: after the segment's last, `o`
    have hlastF : BootEvAt C i F.length e := by
      cases o with
      | none =>
        have : F = [] := by
          rw [← hFd, List.filter_eq_nil_iff]
          intro x hx; simpa using hlast x hx
        subst this
        exact hnext
      | some x =>
        obtain ⟨L1, L2, hL, hxn, hL2⟩ := hlast
        have hF' : F = L1.filter (fun x => decide (x.nid = decStr i)) ++ [x] := by
          rw [← hFd, hL, List.filter_append, List.filter_cons]
          have : L2.filter (fun x => decide (x.nid = decStr i)) = [] := by
            rw [List.filter_eq_nil_iff]; intro y hy; simpa using hL2 y hy
          simp [hxn, this]
        have hlen : F.length = (L1.filter (fun x => decide (x.nid = decStr i))).length + 1 := by
          rw [hF']; simp
        have hx := hF (L1.filter (fun x => decide (x.nid = decStr i))).length (by omega)
        have hxF : F[(L1.filter (fun x => decide (x.nid = decStr i))).length]'(by omega) = x := by
          simp only [hF', List.getElem_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        rw [hxF] at hx
        rw [hlen]
        exact hnext _ hx
    intro k hk
    simp only [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_or_ge k F.length with hkl | hkl
    · rw [List.getElem_append_left hkl]; exact hF k hkl
    · have : k = F.length := by omega
      subst this
      rw [List.getElem_append_right (Nat.le_refl _)]
      simpa using hlastF
  · rw [bootSeg_snoc_ne L e i (by rw [hnid]; exact fun h => hii (decStr_inj h).symm)]
    exact hs.2 i hi

/-- **A bootstrap event holds one position** (`BootEvAt` tells the positions apart by name, term and the
new configuration's size): what a hook's caller needs to discharge `BootNext` from its `Λ`. -/
theorem bootEvAt_unique (C : List w64) (i : w64) (x : TraceEv) :
    ∀ k k', BootEvAt C i k x → BootEvAt C i k' x → k = k' := by
  intro k k' h h'
  match k, k', h, h' with
  | 0, 0, _, _ => rfl
  | 1, 1, _, _ => rfl
  | 2, 2, _, _ => rfl
  | 3, 3, _, _ => rfl
  | 0, 1, h, h' => exact absurd (h.2.1.symm.trans h'.2.1) (by decide)
  | 0, 2, h, h' => exact absurd (h.2.1.symm.trans h'.2.1) (by decide)
  | 0, 3, h, h' => exact absurd (h.2.1.symm.trans h'.2.1) (by decide)
  | 0, _ + 4, h, h' => exact absurd (h.2.1.symm.trans h'.2.2.1) (by decide)
  | 1, 0, h, h' => exact absurd (h.2.1.symm.trans h'.2.1) (by decide)
  | 1, 2, h, h' => exact absurd (h.2.1.symm.trans h'.2.1) (by decide)
  | 1, 3, h, h' => exact absurd (h.2.1.symm.trans h'.2.1) (by decide)
  | 1, q + 4, h, h' =>
    exfalso
    obtain ⟨hq, -, -, -, -, -, -, -, ns, hns, hcc⟩ := h'
    rw [h.2.2.2] at hcc
    have := congrArg (fun c : Option TraceCC => c.map (fun c => c.newconf.length)) hcc
    simp at this
    have := hns.length_eq; simp at this; omega
  | 2, 0, h, h' => exact absurd (h.2.1.symm.trans h'.2.1) (by decide)
  | 2, 1, h, h' => exact absurd (h.2.1.symm.trans h'.2.1) (by decide)
  | 2, 3, h, h' => exact absurd (h.2.2.symm.trans h'.2.2) (by decide)
  | 2, _ + 4, h, h' => exact absurd (h.2.1.symm.trans h'.2.2.1) (by decide)
  | 3, 0, h, h' => exact absurd (h.2.1.symm.trans h'.2.1) (by decide)
  | 3, 1, h, h' => exact absurd (h.2.1.symm.trans h'.2.1) (by decide)
  | 3, 2, h, h' => exact absurd (h.2.2.symm.trans h'.2.2) (by decide)
  | 3, _ + 4, h, h' => exact absurd (h.2.1.symm.trans h'.2.2.1) (by decide)
  | _ + 4, 0, h, h' => exact absurd (h.2.2.1.symm.trans h'.2.1) (by decide)
  | q + 4, 1, h, h' =>
    exfalso
    obtain ⟨hq, -, -, -, -, -, -, -, ns, hns, hcc⟩ := h
    rw [h'.2.2.2] at hcc
    have := congrArg (fun c : Option TraceCC => c.map (fun c => c.newconf.length)) hcc
    simp at this
    have := hns.length_eq; simp at this; omega
  | _ + 4, 2, h, h' => exact absurd (h.2.2.1.symm.trans h'.2.1) (by decide)
  | _ + 4, 3, h, h' => exact absurd (h.2.2.1.symm.trans h'.2.1) (by decide)
  | q + 4, q' + 4, h, h' =>
    obtain ⟨hq, -, -, -, -, -, -, -, ns, hns, hcc⟩ := h
    obtain ⟨hq', -, -, -, -, -, -, -, ns', hns', hcc'⟩ := h'
    rw [hcc] at hcc'
    have := congrArg (fun c : Option TraceCC => c.map (fun c => c.newconf.length)) hcc'
    simp at this
    have h1 := hns.length_eq; have h2 := hns'.length_eq
    simp at h1 h2; omega

/-- **`BootNext` from the position of the last event** (the callers' discharge: `x` at position `k`, the
event at `k + 1`). -/
theorem bootNext_some (C : List w64) (i : w64) (x e : TraceEv) (k : Nat) (hx : BootEvAt C i k x)
    (he : BootEvAt C i (k + 1) e) : BootNext C i (some x) e := by
  intro k' hk'
  rw [← bootEvAt_unique C i x k k' hx hk']
  exact he

end TraceSim

end EtcdGrove
end Perennial
