/-
Lean-first (no Rocq counterpart). Trace-check's layer D, S7 (2026-11-09): `Main`'s pure obligations.

# What `Main` supplies to `NewTrace` and `CheckTrace`, from the events

`Main` (`examples/raft/tracecheck/main.go`) hands `NewTrace` the converted events `L.map evConv`
(`ConvertEvents`) and `CheckTrace` the trace `t` it returns. Their specs take pure premises:
`NewTrace`'s, every event `Event.Bounded` and fewer than `numBound` events; `CheckTrace`'s,
`Trace.CheckTraceOk t true` (`etcdraft/CheckOk.lean`: the lines outside the bootstrap in scope, the
lines' configuration lists bounded, no evaluation error). `Main` must also know that `newTrace`
succeeds (else it panics) and that the verdict is `TLCOK`. This file derives all of them
(`mainPure`) from facts about raft's events `L : List TraceEv`, stated in raft's values, which
layer B's simulation is to export at the end of the run (`notes/trace-validation-plan.md`, layer C,
"`Main`'s pure obligations"):

- `RunAccepted L`: the whole trace parses (`newTrace` succeeds) and the run through every line
  (`Trace.RunRel`, one state per line, no branching, the invariants) is on it: `simInv`'s `SimRun`
  once every voter's bootstrap lines are in (`TraceSimEnd.lean`'s `simRun_runAccepted`);
- `ScopeOk L` (P1-P3 of `notes/trace-validation-sim.md`): every event is in scope
  (`TraceEv.InScope`: no `ChangeConf`, no `InitState`, no `MsgSnap` sent), or is bootstrap-named
  and logged while its node had logged only bootstrap-named lines (`Unbooted`, the negation of
  `TraceSim.booted`); kept event by event (`scopeOk_snoc`), as `simInv`'s ASCII clause is;
- `TraceEv.NumsBelow K` of every event (its numbers below `K ≤ numBound = 2^61`) and fewer than
  `numBound` events, from the time receipts and the adequacy theorem's step bound (`n < 2^61`
  steps; Q12 (a), 2026-11-09);
- `TraceEv.ConfsWithin n` of every event, `n < numBound` (raft's: the three voters);
- `BootLogsOk L` (Q12 (a)): an event logged while its node is unbooted (a line `bootstrapOf` may
  flag, whose log `NewTrace` allocates) has a log size below `bootLogBound = 2^40` (raft's: at most
  the voters' bootstrap entries); kept event by event (`bootLogsOk_snoc`).

The ASCII premise of `ConvertEvents` (`TraceEv.Ascii`) is `simInv`'s clause already and is used by
`ConvertEvents.spec` directly; no pure lemma is needed for it.

The scope law (`linesInScope_of_scopeOk`) is where the bootstrap flags enter (the review's S-2): an
event out of scope is bootstrap-named and its node unbooted when it was logged, so `bootstrapOf`
flags its line (its node's first bootstrap-named line is at or before it, its first other line
after it), whatever the events after it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Convert
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.CheckOk

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-! ## The events' facts (what layer B exports at the end of the run)

`TraceEv.InScope`, `ScopeOk`, `TraceEv.NumsBelow`, `TraceEv.ConfsWithin` and `BootLogsOk` are
raft's (`TraceSim.lean`, Q13: `simInv` keeps them, `SimEvents`). -/

/-- The run, whole: the trace of the events parses, and layer B's run reaches its end on it. -/
def RunAccepted (L : List TraceEv) : Prop :=
  ∃ t ts, Etcdraft.newTrace (L.map evConv) = .ok t ∧ t.RunRel t.len ts

/-! ## `NewTrace`'s premises -/

theorem gInt_numOk (K : Nat) (hK : K ≤ 2 ^ 61) (w : w64) (h : uint.nat w < K) : Etcdraft.numOk (gInt w) := by
  unfold Etcdraft.numOk Etcdraft.numBound gInt
  have : uint.nat w < 2 ^ 61 := by omega
  constructor <;> word

/-- A converted event is bounded when raft's numbers are. -/
theorem evConv_bounded (K : Nat) (hK : K ≤ 2 ^ 61) (e : TraceEv) (h : e.NumsBelow K) :
    (evConv e).Bounded := by
  obtain ⟨h1, h2, h3, hm⟩ := h
  refine ⟨gInt_numOk K hK _ h1, gInt_numOk K hK _ h2, gInt_numOk K hK _ h3, ?_⟩
  intro m hm'
  cases hem : e.msg with
  | none => simp [evConv, hem] at hm'
  | some tm =>
    simp only [evConv, hem, Option.map_some, Option.some.injEq] at hm'
    subst hm'
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hm tm hem
    exact ⟨gInt_numOk K hK _ a1, gInt_numOk K hK _ a2, gInt_numOk K hK _ a3, gInt_numOk K hK _ a4,
      gInt_numOk K hK _ a5, gInt_numOk K hK _ a6⟩

/-! ## `ConfsBounded` -/

/-- A converted event's configuration lists are raft's. -/
theorem evConv_confsBounded (n : Nat) (hn : (n : Int) < Etcdraft.numBound) (e : TraceEv)
    (h : e.ConfsWithin n) : (evConv e).ConfsBounded := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [evConv, List.length_map]; omega
  · intro nc hnc
    unfold evConv at hnc
    split at hnc
    · simp at hnc
    · cases hc : e.propCC with
      | none => simp [hc] at hnc
      | some c =>
        simp only [hc, Option.map_some, Option.bind_some, ccConv] at hnc
        split at hnc
        · cases hnc
        · simp only [Option.some.injEq] at hnc
          subst hnc
          have := h2 c hc
          simp only [List.length_map]; omega

theorem confsBounded_of_events {L : List TraceEv} {t : Etcdraft.Trace} (n : Nat)
    (hn : (n : Int) < Etcdraft.numBound) (hnt : Etcdraft.newTrace (L.map evConv) = .ok t)
    (hc : ∀ e ∈ L, e.ConfsWithin n) : t.ConfsBounded := by
  apply Etcdraft.Trace.confsBounded_of_newTrace hnt
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  exact evConv_confsBounded n hn x (hc x hx)

/-! ## The lines in scope -/

theorem mapM_ok_getElem {α β ε : Type} (f : α → Except ε β) :
    ∀ (l : List α) (r : List β), l.mapM f = .ok r →
      r.length = l.length ∧ ∀ k (hk : k < l.length) (hr : k < r.length), f l[k] = .ok r[k] := by
  intro l
  induction l with
  | nil => intro r h; simp [List.mapM_nil, pure, Except.pure] at h; subst h; simp
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
        obtain ⟨hlen, hget⟩ := ih r' hm
        refine ⟨by simp [hlen], ?_⟩
        intro k hk hr
        cases k with
        | zero => simpa using hf
        | succ k => simpa using hget k (by simp at hk; omega) (by simp at hr; omega)

theorem parseLine_idx (k k' : Nat) (ev : Etcdraft.Event) (ln : Etcdraft.Line)
    (h : Etcdraft.parseLine k ev = .ok ln) : Etcdraft.parseLine k' ev = .ok ln := by
  unfold Etcdraft.parseLine at h ⊢
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h ⊢
  repeat' (first | (split at h) | (split) | (cases h; rfl) | (cases h) | rfl)
  all_goals simp_all

theorem parseLine_nid (k : Nat) (ev : Etcdraft.Event) (ln : Etcdraft.Line)
    (h : Etcdraft.parseLine k ev = .ok ln) : Etcdraft.parseID ev.nid = some ln.nid := by
  unfold Etcdraft.parseLine at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (first | (split at h) | (cases h; done) | (injection h with h; subst h; assumption))

/-- Every line's node is a server of the trace. -/
theorem newTraceWith_nid_mem (evs : List Etcdraft.Event) (pv cq : Bool) (t : Etcdraft.Trace)
    (h : Etcdraft.newTraceWith evs pv cq = .ok t) : ∀ ln ∈ t.lines, ln.nid ∈ t.server := by
  unfold Etcdraft.newTraceWith at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (split at h)
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; intro ln hln
       exact (Etcdraft.SetIds.mem_mk _ _).2 (List.mem_append_left _ (List.mem_map_of_mem hln)))

/-- The first position (from 1) where `P` holds in `bIdx lines` is at or before a position where it
holds. -/
theorem bIdx_find_le (lines : List Etcdraft.Line) (P : Nat × Etcdraft.Line → Bool) (k : Nat)
    (hk : k < lines.length) (hP : P (k + 1, lines.getD k default) = true) :
    (((Etcdraft.bIdx lines).find? P).map Prod.fst).getD 0 ≤ k + 1 ∧
      (((Etcdraft.bIdx lines).find? P).map Prod.fst).getD 0 ≠ 0 := by
  cases hf : (Etcdraft.bIdx lines).find? P with
  | none =>
    have := List.find?_eq_none.1 hf (k + 1, lines.getD k default)
      (List.mem_of_getElem? (Etcdraft.bIdx_getElem? lines k hk))
    exact absurd (by rw [hP]) this
  | some q =>
    obtain ⟨-, xs, ys, hI, hxs⟩ := List.find?_eq_some_iff_append.1 hf
    have hlen : xs.length < (Etcdraft.bIdx lines).length := by rw [hI]; simp
    have hq : (Etcdraft.bIdx lines)[xs.length]? = some q := by rw [hI]; simp
    rw [Etcdraft.bIdx_getElem? lines xs.length (by rw [Etcdraft.bIdx_length] at hlen; exact hlen)] at hq
    cases hq
    simp only [Option.map_some, Option.getD_some]
    refine ⟨?_, by omega⟩
    rcases Nat.lt_or_ge k xs.length with h | h
    · exfalso
      have hm : (k + 1, lines.getD k default) ∈ xs := by
        have h1 : (Etcdraft.bIdx lines)[k]? = xs[k]? := by rw [hI, List.getElem?_append_left h]
        rw [Etcdraft.bIdx_getElem? lines k hk] at h1
        exact List.mem_of_getElem? h1.symm
      have := hxs _ hm
      rw [hP] at this; cases this
    · omega

/-- A bootstrap-named line whose node has logged only bootstrap-named lines before it is one of its
node's bootstrap lines, whatever the lines after it. -/
theorem bootstrapOf_unbooted (lines : List Etcdraft.Line) (k : Nat) (hk : k < lines.length)
    (hbn : Etcdraft.isBootstrapName (lines.getD k default).ev.name = true)
    (hpre : ∀ j < k, (lines.getD j default).nid = (lines.getD k default).nid →
      Etcdraft.isBootstrapName (lines.getD j default).ev.name = true) :
    ((Etcdraft.bootstrapOf lines (lines.getD k default).nid).1).getD k false = true := by
  rw [Etcdraft.bootstrapOf_flag lines _ k hk]
  have hfirst := bIdx_find_le lines
    (fun p => p.2.nid == (lines.getD k default).nid && Etcdraft.isBootstrapName p.2.ev.name) k hk
    (by simp only [beq_self_eq_true, Bool.true_and]; exact hbn)
  have hup : k + 1 ≤ Etcdraft.bUpper lines (lines.getD k default).nid := by
    unfold Etcdraft.bUpper Etcdraft.bFirstNon
    cases hf : (Etcdraft.bIdx lines).find?
        (fun p => p.2.nid == (lines.getD k default).nid && !Etcdraft.isBootstrapName p.2.ev.name) with
    | none => simp; omega
    | some q =>
      obtain ⟨hq1, xs, ys, hI, -⟩ := List.find?_eq_some_iff_append.1 hf
      have hlen : xs.length < lines.length := by
        have : xs.length < (Etcdraft.bIdx lines).length := by rw [hI]; simp
        rwa [Etcdraft.bIdx_length] at this
      have hq : (Etcdraft.bIdx lines)[xs.length]? = some q := by rw [hI]; simp
      rw [Etcdraft.bIdx_getElem? lines xs.length hlen] at hq
      cases hq
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hq1
      obtain ⟨hn, hb⟩ := hq1
      have hgt : k < xs.length := by
        rcases Nat.lt_trichotomy xs.length k with h | h | h
        · have := hpre xs.length h hn; rw [hb] at this; cases this
        · subst h; rw [hb] at hbn; cases hbn
        · exact h
      simp only [Option.map_some, Option.getD_some, bne_iff_ne, ne_eq, Nat.add_one_ne_zero,
        not_false_eq_true, ↓reduceIte]
      omega
  unfold Etcdraft.bIsB Etcdraft.bFirst
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_self_eq_true, and_true]
  exact ⟨by omega, hup⟩

/-- **The lines in scope, from the events** (the review's S-2): a line out of scope is a bootstrap
line of its node, given `ScopeOk` of the events. -/
theorem linesInScope_of_scopeOk {L : List TraceEv} {t : Etcdraft.Trace}
    (hnt : Etcdraft.newTrace (L.map evConv) = .ok t) (hs : ScopeOk L) : t.LinesInScope := by
  obtain ⟨hparse, hboot⟩ := Etcdraft.newTraceWith_ok _ false false t hnt
  obtain ⟨hlen, hget⟩ := mapM_ok_getElem _ _ _ hparse
  simp only [List.length_zip, List.length_range, List.length_map, Nat.min_self] at hlen
  -- line `k` is event `k`'s, parsed at `k`
  have hline : ∀ k (hk : k < L.length), Etcdraft.parseLine k (evConv L[k]) = .ok (t.lines.getD k default) := by
    intro k hk
    have := hget k (by simp; exact hk) (by omega)
    simp only [List.getElem_zip, List.getElem_range, List.getElem_map] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact this
  intro l hl1 hl hb
  unfold Etcdraft.Trace.len at hl
  have hk : l - 1 < L.length := by omega
  have hev : (t.line l).ev = evConv L[l - 1] := Etcdraft.parseLine_ev (hline (l - 1) hk)
  rcases hs (l - 1) hk with hin | ⟨hbn, hun⟩
  · obtain ⟨h1, h2, h3⟩ := hin
    refine ⟨?_, ?_, ?_⟩
    · rw [hev]; exact h1
    · rw [hev]; exact h2
    · rw [hev]; intro hn hsnap
      cases hm : L[l - 1].msg with
      | none => simp [evConv, hm] at hsnap
      | some m =>
        simp only [evConv, hm, Option.map_some, Option.some.injEq] at hsnap
        exact h3 hn m hm hsnap
  · -- a bootstrap line of its node: the flag is set
    exfalso
    have hflag : t.bootstrap.getD (l - 1) false = true := by
      rw [hboot]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (by omega : l - 1 < t.lines.length), Option.map_some, Option.getD_some,
        List.any_map, List.any_eq_true, Function.comp]
      refine ⟨(t.lines.getD (l - 1) default).nid,
        newTraceWith_nid_mem _ false false t hnt _ (by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact List.getElem_mem _), ?_⟩
      have := bootstrapOf_unbooted t.lines (l - 1) (by omega) (by rw [Etcdraft.parseLine_ev (hline (l - 1) hk)]; exact hbn)
        (by
          intro j hj hn
          have hj' : j < L.length := by omega
          have hlj := hline j hj'
          have hnid := parseLine_nid _ _ _ (hline (l - 1) hk)
          exact hun _ hnid L[j]
            (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact List.getElem?_eq_getElem hj')) _
            (parseLine_idx _ 0 _ _ hlj) hn)
      simpa [List.getD_eq_getElem?_getD] using this
    unfold Etcdraft.Trace.line at hev
    rw [hflag] at hb; cases hb

/-! ## The bootstrap logs (`NewTrace`'s allocation) -/

/-- `NewTrace`'s allocation premise of the converted events, from `BootLogsOk`. -/
theorem bootLogsOk_events {L : List TraceEv} (h : BootLogsOk L) : Etcdraft.Event.BootLogsOk (L.map evConv) := by
  intro k hk hbn hpre
  have hk' : k < L.length := by simpa using hk
  simp only [List.getElem_map] at hbn hpre ⊢
  have hlog := h k hk' (by simpa [evConv] using hbn) (by
    intro i hi x hx ln hln hni
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hjk : j < k := by simp at hj; omega
    simp only [List.getElem_take] at hln ⊢
    have hb := hpre j hjk (by
      rw [parseLine_nid _ _ _ hln, hni]
      simpa [evConv] using hi.symm)
    rw [Etcdraft.parseLine_ev hln]; exact hb)
  unfold Etcdraft.bootLogBound
  simp only [evConv, gInt]
  word

/-! ## The combination -/

/-- **`Main`'s pure obligations, together**: from layer B's facts about raft's events at the end of
the run (the run through every line, the events in scope, their numbers below `K ≤ 2^61`, fewer than
`numBound` of them, their configuration lists within `n < numBound`, the logs of the lines that may be
bootstrap lines below `2^40`), `NewTrace`'s premises on the converted events, its success,
`CheckTrace`'s premise on the trace, the search's verdict (its only result is `TLCOK`) and the
corollary `TraceAccepts`. -/
theorem mainPure (L : List TraceEv) (K n : Nat) (hK : K ≤ 2 ^ 61) (hn : (n : Int) < Etcdraft.numBound)
    (hrun : RunAccepted L) (hscope : ScopeOk L) (hnums : ∀ e ∈ L, e.NumsBelow K)
    (hlen : (L.length : Int) < Etcdraft.numBound) (hconf : ∀ e ∈ L, e.ConfsWithin n)
    (hboot : BootLogsOk L) :
    (∀ e ∈ L.map evConv, e.Bounded) ∧ ((L.map evConv).length : Int) < Etcdraft.numBound ∧
    Etcdraft.Event.BootLogsOk (L.map evConv) ∧
    ∃ t, Etcdraft.newTrace (L.map evConv) = .ok t ∧ t.CheckTraceOk true ∧
      (∀ res, Etcdraft.CheckTraceRel t true res → res = { ok := true }) ∧
      Etcdraft.TraceAccepts (L.map evConv) false false := by
  obtain ⟨t, ts, hnt, hr⟩ := hrun
  refine ⟨?_, by simpa using hlen, bootLogsOk_events hboot, t, hnt, ?_, hr.checkTraceRel_eq, ?_⟩
  · intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    exact evConv_bounded K hK x (hnums x hx)
  · exact Etcdraft.Trace.RunRel.checkTraceOk (linesInScope_of_scopeOk hnt hscope)
      (confsBounded_of_events n hn hnt hconf) hr
  · obtain ⟨res, hres, hok⟩ := hr.accepts
    exact ⟨t, hnt, res, hres, hok⟩

end pure

end TraceCheck
end EtcdGrove
end Perennial
