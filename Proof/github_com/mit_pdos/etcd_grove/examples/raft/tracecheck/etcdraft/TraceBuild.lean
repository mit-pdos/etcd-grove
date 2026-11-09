/-
Lean-first (no Rocq counterpart).

# Building a trace: what `NewTraceWith` builds, and the pure facts its proof uses (layer C, 2026-11-09)

`traceHeapRO`: a Go `*Trace` holding a trace, without `traceRO`'s `Trace.Valid` (which is about
`newTrace`, PreVote and CheckQuorum off: `NewTraceWith`'s spec, for any flags, gives the heap part,
and `NewTrace`'s adds the rest). The pure lemmas relate `newTraceWith`'s steps to the Go's loops.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.TraceRead

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- A Go `*Trace` holding `tr`, read-only: `traceRO` without `Trace.Valid`. -/
def traceHeapRO (t : Loc) (tr : Trace) : IProp GF :=
  iprop(∃ g : G.Trace, t ↦□ g ∗
    (∃ lns : List G.line, g.lines' ↦*□ lns ∗ [∗list] ln;x ∈ lns;tr.lines, lineRO ln x) ∗
    setRO g.Server' tr.server ∗ setRO g.InitSrv' tr.initSrv ∗ g.bootstrap' ↦*□ tr.bootstrap ∗
    stateRO g.init' tr.init)

instance traceHeapRO_persistent (t : Loc) (tr : Trace) : Persistent (traceHeapRO (GF := GF) t tr) := by
  unfold traceHeapRO; infer_instance

theorem traceRO_of_heap (t : Loc) (tr : Trace) (h : tr.Valid) :
    traceHeapRO (GF := GF) t tr ⊢ traceRO t tr := by
  unfold traceHeapRO traceRO
  iintro H
  isplitr
  · ipureintro; exact h
  iexact H

end defs

/-! ## Proof tactics (hygiene off: they name the proof's hypotheses) -/

set_option hygiene false in
/-- In `NewTraceWith`'s proof, inside a loop: `traceError(...)` returned out of the loop and the
function, where `h : ∃ e, newTraceWith evs pv cq = .error e`. -/
macro "loop_fail" h:term : tactic => `(tactic| (
  wp_apply wp_traceError as %e %He
  try wp_auto
  wp_for_post
  try wp_auto
  try (wp_for_post; try wp_auto)
  iapply HΦ
  obtain ⟨e', he'⟩ := ($h : ∃ e, newTraceWith evs pv cq = .error e)
  rw [he']; ipureintro; exact He))

/-- `parseLine` fails, by `simp` with the given facts. -/
macro "parse_fails" "[" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp [parseLine, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, $xs,*]))

/-! ## The lines -/

/-- `parseLine`'s checks of the message pass. -/
def msgPass (x : Event) : Prop :=
  ¬ (isMessageEvent x.name = true ∧ x.msg = none) ∧ ∀ m, x.msg = some m → (raftMsgType m.type).isSome = true

/-- `parseLine`'s checks of a configuration change pass. -/
def ccPass (x : Event) : Prop :=
  x.name = "ChangeConf" → ∃ cc, x.prop.bind EventProps.cc = some cc ∧ cc.changes ≠ some []

section parse
variable {k : Nat} {x : Event} {a b : ID} {c0 c1 : SetIds}
  (hn : parseID x.nid = some a) (hv : parseID x.state.vote = some b)
  (h0 : toSet x.conf.1 = some c0) (h1 : toSet x.conf.2 = some c1)
include hn hv h0 h1

theorem parseLine_err_msg (hm : ¬ msgPass x) : ∃ e, parseLine k x = .error e := by
  unfold msgPass at hm
  cases hmsg : x.msg with
  | none =>
    cases hme : isMessageEvent x.name
    · exact absurd ⟨by simp [hme], fun m h => by simp [hmsg] at h⟩ hm
    · simp [parseLine, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hn, hv, h0, h1, hme, hmsg]
  | some m =>
    cases hty : raftMsgType m.type
    · simp [parseLine, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hn, hv, h0, h1, hmsg, hty]
    · exact absurd ⟨by simp [hmsg], fun m' h => by simp [hmsg] at h; subst h; simp [hty]⟩ hm

theorem msgPass_none (hm : msgPass x) (hmsg : x.msg = none) : isMessageEvent x.name = false := by
  cases h : isMessageEvent x.name
  · rfl
  · exact absurd ⟨h, hmsg⟩ hm.1

theorem msgPass_some (hm : msgPass x) {m : EventMsg} (hmsg : x.msg = some m) :
    ∃ t, raftMsgType m.type = some t :=
  Option.isSome_iff_exists.1 (hm.2 m hmsg)

theorem parseLine_err_cc (hm : msgPass x) (hc : ¬ ccPass x) : ∃ e, parseLine k x = .error e := by
  have hcn : x.name = "ChangeConf" := by
    by_cases h : x.name = "ChangeConf"
    · exact h
    · exact absurd (fun h' => absurd h' h) hc
  have hc' : ∀ cc, x.prop.bind EventProps.cc = some cc → cc.changes = some [] := by
    intro cc hcc
    by_cases h : cc.changes = some []
    · exact h
    · exact absurd (fun _ => ⟨cc, hcc, h⟩) hc
  cases hmsg : x.msg with
  | none =>
    have hime := msgPass_none hn hv h0 h1 hm hmsg
    cases hpc : x.prop.bind EventProps.cc with
    | none =>
      simp [parseLine, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hn, hv, h0, h1, hmsg,
        hime, hcn, hpc, (by decide : isMessageEvent "ChangeConf" = false)]
    | some cc =>
      simp [parseLine, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hn, hv, h0, h1, hmsg,
        hime, hcn, hpc, hc' cc hpc, (by decide : isMessageEvent "ChangeConf" = false)]
  | some m =>
    obtain ⟨t, ht⟩ := msgPass_some hn hv h0 h1 hm hmsg
    cases hpc : x.prop.bind EventProps.cc with
    | none =>
      simp [parseLine, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hn, hv, h0, h1, hmsg,
        ht, hcn, hpc]
    | some cc =>
      simp [parseLine, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, hn, hv, h0, h1, hmsg,
        ht, hcn, hpc, hc' cc hpc]

end parse

set_option hygiene false in
/-- `parseLine` evaluated past the configuration change's checks (`hc : ccPass x`), split on them. -/
macro "cc_split" "[" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  by_cases hcn : x.name = "ChangeConf"
  · obtain ⟨cc, hpc, hch⟩ := hc hcn
    simp [parseLine, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Pure.pure, Except.pure, hn, hv,
      h0, h1, hcn, hpc, hch, (by decide : isMessageEvent "ChangeConf" = false), $xs,*]
  · simp [parseLine, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Pure.pure, Except.pure, hn, hv,
      h0, h1, hcn, $xs,*]))

/-- The message's endpoints a line records (`0, 0` without a message), if they parse. -/
def ftOf (x : Event) : Option (ID × ID) :=
  match x.msg with
  | none => some (0, 0)
  | some m =>
    match parseID m.from, parseID m.to with
    | some f, some t => some (f, t)
    | _, _ => none

section parse2
variable {k : Nat} {x : Event} {a b : ID} {c0 c1 : SetIds}
  (hn : parseID x.nid = some a) (hv : parseID x.state.vote = some b)
  (h0 : toSet x.conf.1 = some c0) (h1 : toSet x.conf.2 = some c1) (hm : msgPass x) (hc : ccPass x)
include hn hv h0 h1 hm hc

theorem parseLine_ok {f t : ID} (hft : ftOf x = some (f, t)) :
    parseLine k x = .ok { ev := x, nid := a, vote := b, role := x.role, conf := (c0, c1), «from» := f, to := t } := by
  cases hmsg : x.msg with
  | none =>
    have hime := msgPass_none hn hv h0 h1 hm hmsg
    simp only [ftOf, hmsg, Option.some.injEq, Prod.mk.injEq] at hft
    obtain ⟨rfl, rfl⟩ := hft
    cc_split [hmsg, hime]
  | some m =>
    obtain ⟨ty, hty⟩ := msgPass_some hn hv h0 h1 hm hmsg
    simp only [ftOf, hmsg] at hft
    cases hf : parseID m.from <;> cases ht : parseID m.to <;> simp only [hf, ht, reduceCtorEq] at hft
    simp only [Option.some.injEq, Prod.mk.injEq] at hft
    obtain ⟨rfl, rfl⟩ := hft
    cc_split [hmsg, hty, hf, ht]

theorem parseLine_err_ft (hft : ftOf x = none) : ∃ e, parseLine k x = .error e := by
  cases hmsg : x.msg with
  | none => simp [ftOf, hmsg] at hft
  | some m =>
    obtain ⟨ty, hty⟩ := msgPass_some hn hv h0 h1 hm hmsg
    simp only [ftOf, hmsg] at hft
    cases hf : parseID m.from
    · cc_split [hmsg, hty, hf]
    · cases ht : parseID m.to
      · cc_split [hmsg, hty, hf, ht]
      · simp [hf, ht] at hft

end parse2

theorem zip_range_take_succ {α : Type} (l : List α) (k : Nat) (x : α) (hx : l[k]? = some x) :
    ((List.range l.length).zip l).take (k + 1) = ((List.range l.length).zip l).take k ++ [(k, x)] := by
  have hk : k < l.length := (List.getElem?_eq_some_iff.1 hx).1
  rw [List.take_add_one]
  congr 1
  simp [hx, hk]
  exact (List.getElem?_eq_some_iff.1 hx).2

/-- `parseLine` over the first `k + 1` events, from the first `k`. -/
theorem parse_ok_step {evs : List Event} {k : Nat} {x : Event} {xs : List Line} {ln : Line}
    (hacc : (((List.range evs.length).zip evs).take k).mapM (fun p => parseLine p.1 p.2) = .ok xs)
    (hx : evs[k]? = some x) (hp : parseLine k x = .ok ln) :
    (((List.range evs.length).zip evs).take (k + 1)).mapM (fun p => parseLine p.1 p.2) = .ok (xs ++ [ln]) := by
  rw [zip_range_take_succ evs k x hx, List.mapM_append, hacc]
  simp [hp, bind, Except.bind, Pure.pure, Except.pure]

/-- A step of the lines' fold that fails: `newTraceWith` fails. -/
theorem parse_err {evs : List Event} (pv cq : Bool) (hne : evs ≠ []) {k : Nat} {x : Event}
    {xs : List Line}
    (hacc : (((List.range evs.length).zip evs).take k).mapM (fun p => parseLine p.1 p.2) = .ok xs)
    (hx : evs[k]? = some x) (hp : ∃ e, parseLine k x = .error e) :
    ∃ e, newTraceWith evs pv cq = .error e := by
  obtain ⟨e, hp⟩ := hp
  have h1 : (((List.range evs.length).zip evs).take (k + 1)).mapM (fun p => parseLine p.1 p.2) =
      .error e := by
    rw [zip_range_take_succ evs k x hx, List.mapM_append, hacc]
    simp [hp, bind, Except.bind]
  have h2 : ((List.range evs.length).zip evs).mapM (fun p => parseLine p.1 p.2) = .error e := by
    rw [← List.take_append_drop (k + 1) ((List.range evs.length).zip evs), List.mapM_append, h1]; rfl
  refine ⟨e, ?_⟩
  have hne' : evs.isEmpty = false := by simpa using hne
  unfold newTraceWith
  simp only [hne', h2, bind, Except.bind]
  rfl

end Etcdraft
end EtcdGrove
end Perennial
