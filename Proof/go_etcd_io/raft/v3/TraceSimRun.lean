/-
Lean-first (no Rocq counterpart). Trace-check's layer B (2026-11-09): extending the simulation's run
by a line (`SimRun`, `TraceSimGhost.lean`): the run over the lines so far transfers to the trace
with one more line (`runRel_congr`, `TraceSimLemmas.lean`), and the new line's check extends it.
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSimLemmas
public import Proof.go_etcd_io.raft.v3.TraceSimGhost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

namespace TraceSim

variable [GooseExts]

theorem parseLines_snoc (evs : List Etcdraft.Event) (e : Etcdraft.Event) (lines : List Etcdraft.Line)
    (ln : Etcdraft.Line) (h : parseLines evs = .ok lines) (he : Etcdraft.parseLine evs.length e = .ok ln) :
    parseLines (evs ++ [e]) = .ok (lines ++ [ln]) := by
  unfold parseLines at *
  rw [List.length_append, List.length_singleton, List.range_succ, List.zip_append (by simp),
    List.mapM_append, h]
  simp [he, bind, Except.bind, pure, Except.pure]

theorem mapM_length_except {α β ε : Type} (f : α → Except ε β) :
    ∀ (l : List α) (r : List β), l.mapM f = .ok r → r.length = l.length := by
  intro l
  induction l with
  | nil => intro r h; simp [List.mapM_nil, pure, Except.pure] at h; subst h; rfl
  | cons a l ih =>
    intro r h
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    cases hf : f a with
    | error e => rw [hf] at h; cases h
    | ok b =>
      rw [hf] at h
      simp only at h
      cases hm : l.mapM f with
      | error e => rw [hm] at h; cases h
      | ok r' =>
        rw [hm] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [ih r' hm]

theorem parseLines_length (evs : List Etcdraft.Event) (lines : List Etcdraft.Line)
    (h : parseLines evs = .ok lines) : lines.length = evs.length := by
  unfold parseLines at h
  have := mapM_length_except _ _ _ h
  simpa using this

/-- The lines' trace and the trace with one more line agree up to the lines. -/
theorem linesTrace_agree (C : List w64) (lines : List Etcdraft.Line) (ln : Etcdraft.Line) (l : Nat)
    (hl1 : 1 ≤ l) (hl : l ≤ lines.length) :
    AgreeTo (linesTrace C lines) (linesTrace C (lines ++ [ln])) l := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro k hk
    simp only [linesTrace, Etcdraft.Trace.line, List.getD_eq_getElem?_getD]
    by_cases hk0 : k = 0
    · subst hk0; simp only [Nat.zero_sub]; rw [List.getElem?_append_left (by omega)]
    · rw [List.getElem?_append_left (by omega)]
  · simp only [linesTrace, bootFlags, List.length_append, List.length_singleton,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega : l - 1 < lines.length + 1),
      List.getElem?_range (by omega : l - 1 < lines.length), Option.map_some, Option.getD_some]
    rw [List.any_map, List.any_map]
    congr 1
    funext i
    exact bootstrapOf_snoc lines ln i (l - 1) (by omega)
  · simp [linesTrace, Etcdraft.Trace.len, hl]
  · simp [linesTrace, Etcdraft.Trace.len]; omega

/-- **The run extended by a line**: from a run over `L` reaching `σ`, a new event `e` whose line
parses, checked from `σ` on the trace with it: one successor `ts'`, no violation, no branching. -/
theorem simRun_snoc (C : List w64) (L : List TraceEv) (e : TraceEv)
    (ln : Etcdraft.Line) (ts ts' : Etcdraft.TState) (info : Etcdraft.StepInfo) (lines : List Etcdraft.Line)
    (hl : parseLines (L.map evConv) = .ok lines) (hr : (linesTrace C lines).RunRel L.length ts)
    (he : Etcdraft.parseLine L.length (evConv e) = .ok ln)
    (hc : (linesTrace C (lines ++ [ln])).CheckLineRel true [ts] ([], {}) (.ok ([ts'], info)))
    (hv : info.violation = none) (hb : info.branched = false) :
    SimRun C (L ++ [e]) ts'.s := by
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hpl : parseLines ((L ++ [e]).map evConv) = .ok (lines ++ [ln]) := by
    rw [List.map_append]; apply parseLines_snoc _ _ _ _ hl; simpa using he
  obtain ⟨hr', -⟩ := runRel_congr (linesTrace C lines) (linesTrace C (lines ++ [ln])) rfl _ _ hr
    (fun l h1 h2 => linesTrace_agree C lines ln l h1 (by omega))
  have hstep := Etcdraft.Trace.RunRel.step L.length ts ts' info hr'
    (by simp [linesTrace, Etcdraft.Trace.len]; omega) hc hv hb
  have hagree : AgreeTo (linesTrace C (lines ++ [ln])) (linesTrace C (lines ++ [ln])) (L.length + 1) :=
    ⟨rfl, fun _ _ => rfl, rfl, by simp [linesTrace, Etcdraft.Trace.len]; omega,
      by simp [linesTrace, Etcdraft.Trace.len]; omega⟩
  obtain ⟨-, hl'⟩ := runRel_congr _ _ rfl _ _ hstep (fun l h1 h2 =>
    ⟨rfl, fun _ _ => rfl, rfl, by simp [linesTrace, Etcdraft.Trace.len]; omega,
      by simp [linesTrace, Etcdraft.Trace.len]; omega⟩)
  right
  exact ⟨lines ++ [ln], ts', hpl, by simpa using hstep, rfl, by simpa using hl'⟩

/-- **The first line**: from the voters' initial state (its invariants holding), a first event whose
line parses and is checked with one successor. -/
theorem simRun_first (C : List w64) (e : TraceEv) (ln : Etcdraft.Line) (ts' : Etcdraft.TState)
    (info : Etcdraft.StepInfo) (hinit : (simInit C).violated = .ok none)
    (he : Etcdraft.parseLine 0 (evConv e) = .ok ln)
    (hc : (linesTrace C [ln]).CheckLineRel true [(linesTrace C [ln]).initState] ([], {}) (.ok ([ts'], info)))
    (hv : info.violation = none) (hb : info.branched = false) :
    SimRun C [e] ts'.s := by
  have hpl : parseLines ([e].map evConv) = .ok [ln] := by
    have := parseLines_snoc [] (evConv e) [] ln (by simp [parseLines, pure, Except.pure]) (by simpa using he)
    simpa using this
  have h0 : (linesTrace C [ln]).RunRel 0 (linesTrace C [ln]).initState := .init hinit
  have hstep := Etcdraft.Trace.RunRel.step 0 _ ts' info h0 (by simp [linesTrace, Etcdraft.Trace.len]) hc hv hb
  obtain ⟨-, hl'⟩ := runRel_congr _ _ rfl _ _ hstep (fun l h1 h2 =>
    ⟨rfl, fun _ _ => rfl, rfl, by simp [linesTrace, Etcdraft.Trace.len]; omega,
      by simp [linesTrace, Etcdraft.Trace.len]; omega⟩)
  right
  exact ⟨[ln], ts', hpl, hstep, rfl, hl'⟩

/-- **A run extended by a line with one successor** (after the first line): the new line `ln`
(of event `e`), from any state of the run's end, has the one successor `σ'`, on the next line,
satisfying the invariants. -/
theorem simRun_snoc_single (C : List w64) (L : List TraceEv) (σ σ' : Etcdraft.State) (e : TraceEv)
    (ln : Etcdraft.Line) (hrun : SimRun C L σ) (hL : L ≠ [])
    (he : Etcdraft.parseLine L.length (evConv e) = .ok ln)
    (hnext : ∀ lines (ts : Etcdraft.TState), parseLines (L.map evConv) = .ok lines → ts.s = σ →
      ts.l = L.length + 1 →
      (linesTrace C (lines ++ [ln])).next ts = .ok [{ s := σ', l := ts.l + 1, pl := ts.l }])
    (hinv : σ'.violated = .ok none) :
    SimRun C (L ++ [e]) σ' := by
  rcases hrun with ⟨hL0, -⟩ | ⟨lines, ts, hl, hr, hσ, hts⟩
  · exact absurd hL0 hL
  have hc := checkLine_single _ ts _ (hnext lines ts hl hσ hts) rfl hinv
  exact simRun_snoc C L e ln ts _ _ lines hl hr he hc rfl rfl

/-- **A run extended by a line with a chain of single successors** (a receive line's rounds). -/
theorem simRun_snoc_chain (C : List w64) (L : List TraceEv) (σ σ' : Etcdraft.State) (e : TraceEv)
    (ln : Etcdraft.Line) (hrun : SimRun C L σ) (hL : L ≠ [])
    (he : Etcdraft.parseLine L.length (evConv e) = .ok ln)
    (hchain : ∀ lines (ts : Etcdraft.TState), parseLines (L.map evConv) = .ok lines → ts.s = σ →
      ts.l = L.length + 1 → ∃ tsF : Etcdraft.TState, tsF.s = σ' ∧
        Chain (linesTrace C (lines ++ [ln])) ts.l [ts] ts tsF) :
    SimRun C (L ++ [e]) σ' := by
  rcases hrun with ⟨hL0, -⟩ | ⟨lines, ts, hl, hr, hσ, hts⟩
  · exact absurd hL0 hL
  obtain ⟨tsF, hF, hc⟩ := hchain lines ts hl hσ hts
  have := simRun_snoc C L e ln ts tsF _ lines hl hr he (checkLine_of_chain _ ts tsF hc) rfl rfl
  rw [hF] at this; exact this

/-- **A line past its node's bootstrap segment is no bootstrap line**: line `k` (from 0) of node `i`,
with a line of `i` at or before it whose name is not a bootstrap name. -/
theorem bootstrapOf_past (lines : List Etcdraft.Line) (j : Etcdraft.ID) (k k' : Nat) (hk : k < lines.length)
    (hk' : k' ≤ k) (hn' : (lines.getD k' default).nid = (lines.getD k default).nid)
    (hb' : Etcdraft.isBootstrapName (lines.getD k' default).ev.name = false) :
    ((Etcdraft.bootstrapOf lines j).1).getD k false = false := by
  unfold Etcdraft.bootstrapOf
  simp only [List.getD_eq_getElem?_getD] at hn' hb' ⊢
  simp only [List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]
  by_cases hj : (lines[k]?.getD default).nid = j
  · -- the node's first non-bootstrap line is at or before `k'`
    generalize hI : (List.range lines.length).map (fun k => (k + 1, lines[k]?.getD default)) = I
    have hIl : I.length = lines.length := by rw [← hI]; simp
    have hfst : ∀ m (h : m < I.length), I[m].1 = m + 1 := by intro m h; subst hI; simp
    have hIk' : I[k']'(by omega) = (k' + 1, lines[k']?.getD default) := by subst hI; simp
    cases hf : I.find? (fun p => p.2.nid == j && !Etcdraft.isBootstrapName p.2.ev.name) with
    | none =>
      have := List.find?_eq_none.1 hf (I[k']'(by omega)) (List.getElem_mem _)
      rw [hIk'] at this; simp [hn', hj, hb'] at this
    | some q =>
      have hle := find_first_le I hfst _ q hf k' (by omega) (by rw [hIk']; simp [hn', hj, hb'])
      have hq0 : q.1 ≠ 0 := by
        obtain ⟨-, xs1, ys1, hI', -⟩ := List.find?_eq_some_iff_append.1 hf
        have : I[xs1.length]'(by rw [hI']; simp) = q := by simp [hI']
        rw [← this, hfst]; omega
      simp only [Option.map_some, Option.getD_some, bne_iff_ne, ne_eq, hq0, not_false_eq_true, ↓reduceIte,
        Bool.and_eq_false_iff, decide_eq_false_iff_not]
      left; right; omega
  · simp [hj]

theorem bootFlags_past (srv : Etcdraft.SetIds) (lines : List Etcdraft.Line) (k k' : Nat) (hk : k < lines.length)
    (hk' : k' ≤ k) (hn' : (lines.getD k' default).nid = (lines.getD k default).nid)
    (hb' : Etcdraft.isBootstrapName (lines.getD k' default).ev.name = false) :
    (bootFlags srv lines).getD k false = false := by
  unfold bootFlags
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some, List.any_eq_false, List.mem_map]
  rintro _ ⟨j, -, rfl⟩
  have := bootstrapOf_past lines j k k' hk hk' hn' hb'
  simpa [List.getD_eq_getElem?_getD] using this

/-- **A non-bootstrap-named line is no bootstrap line.** -/
theorem bootFlags_nonBoot (srv : Etcdraft.SetIds) (lines : List Etcdraft.Line) (ln : Etcdraft.Line)
    (hb : Etcdraft.isBootstrapName ln.ev.name = false) :
    (bootFlags srv (lines ++ [ln])).getD lines.length false = false :=
  bootFlags_past srv (lines ++ [ln]) lines.length lines.length (by simp) (Nat.le_refl _) rfl
    (by simpa [List.getD_eq_getElem?_getD] using hb)

end TraceSim

end EtcdGrove
end Perennial
