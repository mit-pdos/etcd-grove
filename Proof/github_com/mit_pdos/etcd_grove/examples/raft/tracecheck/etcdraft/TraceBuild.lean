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

set_option hygiene false in
/-- In `NewTraceWith`'s server loop, a case of the `ChangeConf` check that adds no server (`addedServer`
returns `none`, by `simp` with the given facts; `ho : addedServer xl = .ok o`): the join's assertion,
the server list unchanged. -/
macro "skip_leaf" "[" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  have ho' : addedServer xl = .ok none := by
    simp [addedServer, Pure.pure, Except.pure, $xs,*]
  rw [ho'] at ho; cases ho
  wp_join_done
  iexists _, _
  iframe
  ipureintro; simp))

theorem isBN_cases (s : String) : s = "InitState" ∨ (s ≠ "InitState" ∧ s = "BecomeFollower") ∨
    (s ≠ "InitState" ∧ s ≠ "BecomeFollower" ∧ s = "ApplyConfChange") ∨
    (s ≠ "InitState" ∧ s ≠ "BecomeFollower" ∧ s ≠ "ApplyConfChange") := by
  by_cases h1 : s = "InitState"
  · exact .inl h1
  by_cases h2 : s = "BecomeFollower"
  · exact .inr (.inl ⟨h1, h2⟩)
  by_cases h3 : s = "ApplyConfChange"
  · exact .inr (.inr (.inl ⟨h1, h2, h3⟩))
  exact .inr (.inr (.inr ⟨h1, h2, h3⟩))

set_option hygiene false in
/-- At a call of `NewTraceWith`'s closure `isBootstrapName` on a Go string `H : strRel gs name` holds
(stepped into by `wp_auto`, its first comparison pending): its comparisons, in four cases, each
leaving `hb : isBootstrapName name = b` and the call's result `#b`. -/
macro "isbn_eval" H:term "," name:term : tactic => `(tactic| (
  rw [decide_strRel $H (show strRel go!"InitState" "InitState" by strRel_lit)]
  rcases isBN_cases $name with hb1 | ⟨hb1, hb2⟩ | ⟨hb1, hb2, hb3⟩ | ⟨hb1, hb2, hb3⟩
  all_goals first
    | (rw [decide_eq_false hb1]; wp_auto
       rw [decide_strRel $H (show strRel go!"BecomeFollower" "BecomeFollower" by strRel_lit), decide_eq_false hb2]
       wp_auto
       rw [decide_strRel $H (show strRel go!"ApplyConfChange" "ApplyConfChange" by strRel_lit), decide_eq_false hb3]
       wp_auto
       have hb : isBootstrapName $name = false := by simp [isBootstrapName, hb1, hb2, hb3])
    | (rw [decide_eq_false hb1]; wp_auto
       rw [decide_strRel $H (show strRel go!"BecomeFollower" "BecomeFollower" by strRel_lit), decide_eq_false hb2]
       wp_auto
       rw [decide_strRel $H (show strRel go!"ApplyConfChange" "ApplyConfChange" by strRel_lit), decide_eq_true hb3]
       wp_auto
       have hb : isBootstrapName $name = true := by simp [isBootstrapName, hb3])
    | (rw [decide_eq_false hb1]; wp_auto
       rw [decide_strRel $H (show strRel go!"BecomeFollower" "BecomeFollower" by strRel_lit), decide_eq_true hb2]
       wp_auto
       have hb : isBootstrapName $name = true := by simp [isBootstrapName, hb2])
    | (rw [decide_eq_true hb1]; wp_auto
       have hb : isBootstrapName $name = true := by simp [isBootstrapName, hb1])))

set_option hygiene false in
/-- In `NewTraceWith`'s closure `bootstrappedConfig` (a join on its result, its map `Hlm`): an error
returned, `tBC` failing by `simp` with the given facts. -/
macro "bc_fail" "[" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  try (wp_apply wp_map_lookup1 $$ [Hlm] as Hlm
       · iexact Hlm)
  try wp_auto
  wp_apply wp_traceError as %e %He
  try wp_auto
  iexists _, _
  iframe Hlm
  isplitl []
  · ipureintro; rfl
  simp [throw, throwThe, MonadExceptOf.throw, $xs,*]
  ipureintro; exact He))

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

/-! ## Folds a step at a time -/

theorem mapM_take_succ_ok {α β ε : Type} (f : α → Except ε β) (l : List α) (m : Nat) (a : α) (r : List β)
    (b : β) (hl : l[m]? = some a) (h : (l.take m).mapM f = .ok r) (hf : f a = .ok b) :
    (l.take (m + 1)).mapM f = .ok (r ++ [b]) := by
  rw [List.take_add_one, hl, Option.toList_some, List.mapM_append, h]
  simp [hf, bind, Except.bind, Pure.pure, Except.pure]

theorem mapM_take_succ_err {α β ε : Type} (f : α → Except ε β) (l : List α) (m : Nat) (a : α) (r : List β)
    (e : ε) (hl : l[m]? = some a) (h : (l.take m).mapM f = .ok r) (hf : f a = .error e) :
    l.mapM f = .error e := by
  have h1 : (l.take (m + 1)).mapM f = .error e := by
    rw [List.take_add_one, hl, Option.toList_some, List.mapM_append, h]
    simp [hf, bind, Except.bind]
  rw [← List.take_append_drop (m + 1) l, List.mapM_append, h1]; rfl

/-! ## The servers -/

theorem insertSorted_mem_self (id : ID) : ∀ s : SetIds, id ∈ insertSorted id s
  | [] => by simp [insertSorted]
  | y :: ys => by
    unfold insertSorted
    split
    · simp
    · split
      · rename_i h; simp [h]
      · exact List.mem_cons_of_mem _ (insertSorted_mem_self id ys)

theorem insertSorted_mem_of_mem (id x : ID) : ∀ s : SetIds, x ∈ s → x ∈ insertSorted id s
  | [], h => by simp at h
  | y :: ys, h => by
    unfold insertSorted
    split
    · exact List.mem_cons_of_mem _ h
    · split
      · exact h
      · rcases List.mem_cons.1 h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (insertSorted_mem_of_mem id x ys h)

theorem foldl_insertSorted_mem (z : ID) : ∀ (l : List ID) (s : SetIds),
    z ∈ l.foldl (fun s id => insertSorted id s) s ↔ z ∈ s ∨ z ∈ l
  | [], s => by simp
  | x :: xs, s => by
    rw [List.foldl_cons, foldl_insertSorted_mem z xs]
    constructor
    · rintro (h | h)
      · rcases insertSorted_mem x z s h with rfl | h
        · exact .inr List.mem_cons_self
        · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)
    · rintro (h | h)
      · exact .inl (insertSorted_mem_of_mem x z s h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact .inl (insertSorted_mem_self _ s)
        · exact .inr h

theorem SetIds.mem_mk (z : ID) (l : List ID) : z ∈ SetIds.mk l ↔ z ∈ l := by
  unfold SetIds.mk; rw [foldl_insertSorted_mem]; simp

theorem sorted_eq_of_mem_iff : ∀ (l1 l2 : List ID), l1.Pairwise (· < ·) → l2.Pairwise (· < ·) →
    (∀ z, z ∈ l1 ↔ z ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 List.mem_cons_self) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 List.mem_cons_self) (by simp)
  | a :: l1, b :: l2, h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 List.mem_cons_self) with e | ha
      · exact e
      · rcases List.mem_cons.1 ((h b).2 List.mem_cons_self) with e | hb
        · exact e.symm
        · exact absurd (Nat.lt_trans (h2.1 a ha) (h1.1 b hb)) (Nat.lt_irrefl _)
    subst hab
    congr 1
    refine sorted_eq_of_mem_iff l1 l2 h1.2 h2.2 (fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
    · rcases List.mem_cons.1 ((h z).1 (List.mem_cons_of_mem _ hz)) with e | e
      · subst e; exact absurd (h1.1 _ hz) (Nat.lt_irrefl _)
      · exact e
    · rcases List.mem_cons.1 ((h z).2 (List.mem_cons_of_mem _ hz)) with e | e
      · subst e; exact absurd (h2.1 _ hz) (Nat.lt_irrefl _)
      · exact e

/-- `SetIds.mk` depends only on the members of its list. -/
theorem SetIds.mk_congr {l1 l2 : List ID} (h : ∀ z, z ∈ l1 ↔ z ∈ l2) : SetIds.mk l1 = SetIds.mk l2 :=
  sorted_eq_of_mem_iff _ _ (SetIds.mk_sorted l1) (SetIds.mk_sorted l2)
    (fun z => by rw [SetIds.mem_mk, SetIds.mem_mk]; exact h z)

/-- Where `addedServer` fails: a `ChangeConf` whose first change adds a server whose id does not parse. -/
def addedBad (xl : Line) : Prop :=
  xl.ev.name = "ChangeConf" ∧ ∃ c cs, (xl.ev.prop.bind EventProps.cc).bind EventConfChange.changes = some (c :: cs) ∧
    (c.action = "AddNewServer" ∨ c.action = "AddLearner") ∧ parseID c.nid = none

theorem addedServer_bad {xl : Line} (h : addedBad xl) : ∃ e, addedServer xl = .error e := by
  obtain ⟨hn, c, cs, hch, hact, hp⟩ := h
  rcases hact with ha | ha <;> simp [addedServer, hn, hch, ha, hp, throw, throwThe, MonadExceptOf.throw]

theorem addedServer_ok {xl : Line} (h : ¬ addedBad xl) : ∃ o, addedServer xl = .ok o := by
  unfold addedServer
  by_cases hn : xl.ev.name = "ChangeConf"
  · cases hch : (xl.ev.prop.bind EventProps.cc).bind EventConfChange.changes with
    | none => exact ⟨none, by simp [hn, hch, Pure.pure, Except.pure]⟩
    | some l =>
      cases l with
      | nil => exact ⟨none, by simp [hn, hch, Pure.pure, Except.pure]⟩
      | cons c cs =>
        by_cases ha : c.action = "AddNewServer" ∨ c.action = "AddLearner"
        · cases hp : parseID c.nid with
          | none => exact absurd ⟨hn, c, cs, hch, ha, hp⟩ h
          | some j =>
            rcases ha with ha | ha <;> exact ⟨some j, by simp [hn, hch, ha, hp, Pure.pure, Except.pure]⟩
        · have h1 : c.action ≠ "AddNewServer" := fun h' => ha (.inl h')
          have h2 : c.action ≠ "AddLearner" := fun h' => ha (.inr h')
          exact ⟨none, by simp [hn, hch, h1, h2, Pure.pure, Except.pure]⟩
  · exact ⟨none, by simp [hn, Pure.pure, Except.pure]⟩

/-- `addedServer` fails on a line: `newTraceWith` fails. -/
theorem added_err {evs : List Event} (pv cq : Bool) (hne : evs ≠ []) {xs : List Line}
    (hlines : ((List.range evs.length).zip evs).mapM (fun p => parseLine p.1 p.2) = .ok xs)
    {m : Nat} {xl : Line} {ad : List (Option ID)} (hacc : (xs.take m).mapM addedServer = .ok ad)
    (hx : xs[m]? = some xl) (he : ∃ e, addedServer xl = .error e) :
    ∃ e, newTraceWith evs pv cq = .error e := by
  obtain ⟨e, he⟩ := he
  have h2 := mapM_take_succ_err addedServer xs m xl ad e hx hacc he
  refine ⟨e, ?_⟩
  have hne' : evs.isEmpty = false := by simpa using hne
  unfold newTraceWith
  simp only [hne', hlines, h2, bind, Except.bind]
  rfl

/-! ## The bootstrap lines (`bootstrapOf`, as the Go's loops compute it) -/

/-- The lines, numbered from 1. -/
def bIdx (lines : List Line) : List (Nat × Line) :=
  (List.range lines.length).map (fun k => (k + 1, lines.getD k default))

def bFirst (lines : List Line) (i : ID) : Nat :=
  (((bIdx lines).find? (fun p => p.2.nid == i && isBootstrapName p.2.ev.name)).map Prod.fst).getD 0

def bFirstNon (lines : List Line) (i : ID) : Nat :=
  (((bIdx lines).find? (fun p => p.2.nid == i && !isBootstrapName p.2.ev.name)).map Prod.fst).getD 0

def bUpper (lines : List Line) (i : ID) : Nat :=
  if bFirstNon lines i != 0 then bFirstNon lines i - 1 else lines.length

def bIsB (lines : List Line) (i : ID) (p : Nat × Line) : Bool :=
  decide (max (bFirst lines i) 1 ≤ p.1) && decide (p.1 ≤ bUpper lines i) && p.2.nid == i

def bLastF (lines : List Line) (i : ID) (acc : Nat) (p : Nat × Line) : Nat :=
  if bIsB lines i p then p.1 else acc

theorem bootstrapOf_eq (lines : List Line) (i : ID) :
    bootstrapOf lines i = ((bIdx lines).map (bIsB lines i), (bIdx lines).foldl (bLastF lines i) 0) := rfl

theorem bIdx_length (lines : List Line) : (bIdx lines).length = lines.length := by simp [bIdx]

theorem bIdx_getElem? (lines : List Line) (j : Nat) (hj : j < lines.length) :
    (bIdx lines)[j]? = some (j + 1, lines.getD j default) := by
  simp [bIdx, hj]

theorem bIdx_fst_pos {lines : List Line} {p : Nat × Line} (hp : p ∈ bIdx lines) : 1 ≤ p.1 := by
  simp only [bIdx, List.mem_map, List.mem_range] at hp
  obtain ⟨k, _, rfl⟩ := hp; simp

theorem bIdx_take_fst_le {lines : List Line} {j : Nat} {p : Nat × Line} (hp : p ∈ (bIdx lines).take j) :
    p.1 ≤ j := by
  simp only [bIdx, ← List.map_take, List.mem_map, List.take_range, List.mem_range] at hp
  obtain ⟨k, hk, rfl⟩ := hp; simp; omega

theorem bIdx_drop_fst_ge {lines : List Line} {j : Nat} {p : Nat × Line} (hp : p ∈ (bIdx lines).drop j) :
    j + 1 ≤ p.1 := by
  obtain ⟨k, hk, hkp⟩ := List.getElem_of_mem hp
  simp only [List.getElem_drop, List.length_drop, bIdx_length] at hk hkp
  have : (bIdx lines)[j + k]? = some p := by rw [List.getElem?_eq_getElem (by rw [bIdx_length]; omega)]; simp [hkp]
  rw [bIdx_getElem? lines (j + k) (by omega)] at this
  cases this; simp

/-- A step of the Go's search for the first line of a kind: the line found so far, 0 if none. -/
theorem find_fst_step (P : Nat × Line → Bool) (lines : List Line) (j : Nat) (hj : j < lines.length) :
    ((((bIdx lines).take (j + 1)).find? P).map Prod.fst).getD 0 =
      if ((((bIdx lines).take j).find? P).map Prod.fst).getD 0 = 0 ∧ P (j + 1, lines.getD j default) = true
      then j + 1
      else ((((bIdx lines).take j).find? P).map Prod.fst).getD 0 := by
  rw [List.take_add_one, bIdx_getElem? lines j hj, Option.toList_some, List.find?_append]
  cases hf : ((bIdx lines).take j).find? P with
  | none =>
    simp only [Option.none_or, Option.map_none, Option.getD_none, true_and]
    cases hP : P (j + 1, lines.getD j default) <;> simp only [List.find?_cons, List.find?_nil, hP] <;> simp
  | some p =>
    have h1 : 1 ≤ p.1 := bIdx_fst_pos (List.mem_of_mem_take (List.mem_of_find?_eq_some hf))
    have : p.1 ≠ 0 := by omega
    simp [this]

theorem find_fst_le (P : Nat × Line → Bool) (lines : List Line) :
    (((bIdx lines).find? P).map Prod.fst).getD 0 ≤ lines.length := by
  cases hf : (bIdx lines).find? P with
  | none => simp
  | some p =>
    have := bIdx_take_fst_le (j := lines.length) (lines := lines) (p := p)
      (by rw [List.take_of_length_le (by rw [bIdx_length]; exact Nat.le_refl _)]; exact List.mem_of_find?_eq_some hf)
    simpa using this

theorem bFirst_le (lines : List Line) (i : ID) : bFirst lines i ≤ lines.length := find_fst_le _ _
theorem bFirstNon_le (lines : List Line) (i : ID) : bFirstNon lines i ≤ lines.length := find_fst_le _ _
theorem bUpper_le (lines : List Line) (i : ID) : bUpper lines i ≤ lines.length := by
  unfold bUpper; have := bFirstNon_le lines i; split <;> omega

theorem bFirst_full (lines : List Line) (i : ID) :
    bFirst lines i = ((((bIdx lines).take lines.length).find?
      (fun p => p.2.nid == i && isBootstrapName p.2.ev.name)).map Prod.fst).getD 0 := by
  rw [List.take_of_length_le (by rw [bIdx_length]; exact Nat.le_refl _)]; rfl

theorem bFirstNon_full (lines : List Line) (i : ID) :
    bFirstNon lines i = ((((bIdx lines).take lines.length).find?
      (fun p => p.2.nid == i && !isBootstrapName p.2.ev.name)).map Prod.fst).getD 0 := by
  rw [List.take_of_length_le (by rw [bIdx_length]; exact Nat.le_refl _)]; rfl

theorem bIsB_in_range (lines : List Line) (i : ID) (k : Nat) (l : Line) (hk1 : max (bFirst lines i) 1 ≤ k)
    (hk2 : k ≤ bUpper lines i) : bIsB lines i (k, l) = (l.nid == i) := by
  simp [bIsB, hk1, hk2]

theorem bIsB_lt (lines : List Line) (i : ID) (p : Nat × Line) (hk : p.1 < max (bFirst lines i) 1) :
    bIsB lines i p = false := by
  simp [bIsB]; intro h; omega

theorem bIsB_gt (lines : List Line) (i : ID) (p : Nat × Line) (hk : bUpper lines i < p.1) :
    bIsB lines i p = false := by
  simp [bIsB]; intro _ h; omega

theorem foldl_bLastF_const (lines : List Line) (i : ID) :
    ∀ (l : List (Nat × Line)) (acc : Nat), (∀ p ∈ l, bIsB lines i p = false) → l.foldl (bLastF lines i) acc = acc
  | [], _, _ => rfl
  | p :: l, acc, h => by
    rw [List.foldl_cons, show bLastF lines i acc p = acc by simp [bLastF, h p List.mem_cons_self]]
    exact foldl_bLastF_const lines i l acc (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem last_init (lines : List Line) (i : ID) :
    ((bIdx lines).take (max (bFirst lines i) 1 - 1)).foldl (bLastF lines i) 0 = 0 :=
  foldl_bLastF_const lines i _ 0 (fun p hp => bIsB_lt lines i p (by have := bIdx_take_fst_le hp; omega))

theorem last_step (lines : List Line) (i : ID) (j : Nat) (hj : j < lines.length)
    (hk1 : max (bFirst lines i) 1 ≤ j + 1) (hk2 : j + 1 ≤ bUpper lines i) :
    ((bIdx lines).take (j + 1)).foldl (bLastF lines i) 0 =
      if (lines.getD j default).nid == i then j + 1 else ((bIdx lines).take j).foldl (bLastF lines i) 0 := by
  rw [List.take_add_one, bIdx_getElem? lines j hj, Option.toList_some, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, bLastF, bIsB_in_range lines i (j + 1) _ hk1 hk2]

theorem last_end (lines : List Line) (i : ID) (k : Nat) (hk : bUpper lines i < k) :
    (bIdx lines).foldl (bLastF lines i) 0 = ((bIdx lines).take (k - 1)).foldl (bLastF lines i) 0 := by
  conv => lhs; rw [← List.take_append_drop (k - 1) (bIdx lines)]
  rw [List.foldl_append]
  exact foldl_bLastF_const lines i _ _ (fun p hp => bIsB_gt lines i p (by have := bIdx_drop_fst_ge hp; omega))

theorem bootstrapOf_flag (lines : List Line) (i : ID) (j : Nat) (hj : j < lines.length) :
    (bootstrapOf lines i).1.getD j false = bIsB lines i (j + 1, lines.getD j default) := by
  rw [bootstrapOf_eq]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, bIdx_getElem? lines j hj, Option.map_some,
    Option.getD_some]

/-- The Go's bootstrap flags in its loop over server `i` (the `n`-th), at line `k`: those of the
servers before, and server `i`'s below `k`. -/
def bootFlags (xs : List Line) (srv : SetIds) (n : Nat) (i : ID) (k : Nat) : List Bool :=
  (List.range xs.length).map (fun k' => (srv.take n).any (fun j => (bootstrapOf xs j).1.getD k' false) ||
    (decide (k' + 1 < k) && bIsB xs i (k' + 1, xs.getD k' default)))

theorem bootFlags_init (xs : List Line) (srv : SetIds) (n : Nat) (i : ID) :
    bootFlags xs srv n i (max (bFirst xs i) 1) =
      (List.range xs.length).map (fun k' => (srv.take n).any (fun j => (bootstrapOf xs j).1.getD k' false)) := by
  unfold bootFlags
  apply List.map_congr_left
  intro k' _
  by_cases h : k' + 1 < max (bFirst xs i) 1
  · rw [bIsB_lt xs i _ h]; simp
  · simp [h]

theorem bootFlags_skip (xs : List Line) (srv : SetIds) (n : Nat) (i : ID) (k : Nat)
    (hk1 : max (bFirst xs i) 1 ≤ k) (hk2 : k ≤ bUpper xs i) (hne : (xs.getD (k - 1) default).nid ≠ i) :
    bootFlags xs srv n i (k + 1) = bootFlags xs srv n i k := by
  unfold bootFlags
  apply List.map_congr_left
  intro k' _
  by_cases h : k' + 1 = k
  · subst h
    rw [bIsB_in_range xs i _ _ hk1 hk2]
    have e : k' + 1 - 1 = k' := by omega
    rw [e] at hne
    simp only [List.getD_eq_getElem?_getD] at hne
    simp [hne]
  · have : (k' + 1 < k + 1) = (k' + 1 < k) := by apply propext; omega
    simp only [this]

theorem bootFlags_set (xs : List Line) (srv : SetIds) (n : Nat) (i : ID) (k : Nat) (hk0 : 1 ≤ k)
    (hk1 : max (bFirst xs i) 1 ≤ k) (hk2 : k ≤ bUpper xs i) (hkl : k ≤ xs.length)
    (heq : (xs.getD (k - 1) default).nid = i) :
    (bootFlags xs srv n i k).set (k - 1) true = bootFlags xs srv n i (k + 1) := by
  apply List.ext_getElem
  · simp [bootFlags]
  intro k' h1 h2
  rw [List.getElem_set]
  simp only [bootFlags, List.getElem_map, List.getElem_range]
  split
  · rename_i h
    subst h
    rw [bIsB_in_range xs i _ _ (by omega) (by omega)]
    have : k - 1 + 1 = k := by omega
    simp only [List.getD_eq_getElem?_getD] at heq
    simp [this, heq]
  · rename_i h
    have : (k' + 1 < k + 1) = (k' + 1 < k) := by apply propext; omega
    simp only [this]

theorem bootFlags_end (xs : List Line) (srv : SetIds) (n : Nat) (i : ID) (k : Nat)
    (hk : bUpper xs i < k) (hi : srv[n]? = some i) :
    bootFlags xs srv n i k =
      (List.range xs.length).map
        (fun k' => (srv.take (n + 1)).any (fun j => (bootstrapOf xs j).1.getD k' false)) := by
  unfold bootFlags
  apply List.map_congr_left
  intro k' hk'
  rw [List.mem_range] at hk'
  rw [List.take_add_one, hi, Option.toList_some, List.any_append]
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  rw [bootstrapOf_flag xs i k' hk']
  congr 1
  by_cases h : k' + 1 < k
  · simp [h]
  · rw [bIsB_gt xs i _ (by simp; omega)]; simp

theorem nodup_not_mem_take {l : List ID} (hl : l.Nodup) {n : Nat} {x : ID} (hx : l[n]? = some x) :
    x ∉ l.take n := by
  intro hm
  obtain ⟨m, hm1, hm2⟩ := List.getElem_of_mem hm
  simp only [List.length_take] at hm1
  rw [List.getElem_take] at hm2
  have hn : n < l.length := (List.getElem?_eq_some_iff.1 hx).1
  have := hl.eq_of_getElem_eq (i := m) (j := n) (by omega) hn
    (by rw [hm2]; exact ((List.getElem?_eq_some_iff.1 hx).2).symm)
  omega

/-- A server without a bootstrap line: `newTraceWith` fails. -/
theorem boot_err {evs : List Event} (pv cq : Bool) (hne : evs ≠ []) {xs : List Line}
    (hlines : ((List.range evs.length).zip evs).mapM (fun p => parseLine p.1 p.2) = .ok xs)
    {ad : List (Option ID)} (hadd : xs.mapM addedServer = .ok ad) {i : ID}
    (hi : i ∈ SetIds.mk (xs.map Line.nid ++ ad.filterMap id)) (h0 : (bootstrapOf xs i).2 = 0) :
    ∃ e, newTraceWith evs pv cq = .error e := by
  obtain ⟨p, hp⟩ : ∃ p, ((SetIds.mk (xs.map Line.nid ++ ad.filterMap id)).map
      (fun i => (i, bootstrapOf xs i))).find? (fun p => p.2.2 == 0) = some p :=
    Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨(i, bootstrapOf xs i), List.mem_map_of_mem hi, by simp [h0]⟩)
  refine ⟨{ what := "a server without a bootstrap line", line := 0, n := p.1 }, ?_⟩
  have hne' : evs.isEmpty = false := by simpa using hne
  unfold newTraceWith
  simp only [hne', hlines, hadd, bind, Except.bind, hp]
  rfl

/-! ## `newTraceWith` past its lines and servers -/

def tPer (xs : List Line) (srv : SetIds) : List (ID × List Bool × Nat) := srv.map (fun i => (i, bootstrapOf xs i))

def tLast (xs : List Line) (srv : SetIds) (i : ID) : Nat :=
  (((tPer xs srv).find? (fun p => p.1 == i)).map (fun p => p.2.2)).getD 0

/-- `BootstrappedConfig(i)` for the server whose last bootstrap line is `last`. -/
def tBC (xs : List Line) (last : Nat) : Except TraceError SetIds :=
  let ln := xs.getD (last - 1) default
  if ln.ev.name == "ApplyConfChange" then
    match (ln.ev.prop.bind EventProps.cc).bind EventConfChange.newconf with
    | none => throw { what := "a last bootstrap ApplyConfChange without newconf", line := last, n := 0 }
    | some nc => match toSet nc with
      | some c => pure c
      | none => throw { what := "newconf not a list of ids", line := last, n := 0 }
  else pure ln.conf.1

/-- `BootstrapEntryConf`'s configurations of server `i`. -/
def tBconfF (xs : List Line) (srv : SetIds) (i : ID) : Except TraceError (ID × List SetIds) := do
  let flags := (((tPer xs srv).find? (fun p => p.1 == i)).map (fun p => p.2.1)).getD []
  let cs ← ((List.range xs.length).filter (fun k => flags.getD k false)).filterMapM (fun k => do
    let ln := xs.getD k default
    if ln.ev.name != "ApplyConfChange" then return none
    match (ln.ev.prop.bind EventProps.cc).bind EventConfChange.newconf with
    | none => return none
    | some nc => match toSet nc with
      | some c => return some c
      | none => throw { what := "newconf not a list of ids", line := k + 1, n := 0 })
  return (i, cs)

def tServerOf (xs : List Line) (srv : SetIds) (cfgs : List (ID × SetIds)) (bconfs : List (ID × List SetIds))
    (i : ID) : Server :=
  let lb := xs.getD (tLast xs srv i - 1) default
  let cfg := ((cfgs.find? (fun p => p.1 == i)).map Prod.snd).getD []
  let v : Server :=
    { currentTerm := lb.ev.state.term, state := lb.role, votedFor := lb.vote, lead := nil,
      log := (List.range lb.ev.log.toNat).map (fun k =>
        { term := 1, type := .config, value := .conf ((((bconfs.find? (fun p => p.1 == i)).map Prod.snd).getD []).getD k cfg) [] }),
      commitIndex := lb.ev.state.commit, votesResponded := [], votesGranted := [],
      matchIndex := fun _ => 0, pendingConfChangeIndex := 0,
      config := { incoming := cfg, outgoing := [], learners := [] }, durable := default }
  { v with durable := durableOf v }

def newTraceTail (xs : List Line) (srv : SetIds) (pv cq : Bool) : Except TraceError Trace := do
  if let some p := (tPer xs srv).find? (fun p => p.2.2 == 0) then
    throw { what := "a server without a bootstrap line", line := 0, n := p.1 }
  let initSrv ← tBC xs (tLast xs srv (xs.getD 0 default).nid)
  if !initSrv.subset srv then throw { what := "TraceInitServer not a subset of TraceServer", line := 0, n := 0 }
  let cfgs ← srv.mapM (fun i => do return (i, ← tBC xs (tLast xs srv i)))
  let bconfs ← srv.mapM (tBconfF xs srv)
  let bootstrap := (List.range xs.length).map (fun k => (tPer xs srv).any (fun p => p.2.1.getD k false))
  let st : State :=
    { server := srv, s := (fun i => tServerOf xs srv cfgs bconfs i), messages := [], pendingMessages := [],
      reconfigCount := 0, preVote := pv, checkQuorum := cq }
  return { lines := xs, server := srv, initSrv := initSrv, bootstrap := bootstrap, init := st }

theorem newTraceWith_tail {evs : List Event} (pv cq : Bool) (hne : evs ≠ []) {xs : List Line}
    (hlines : ((List.range evs.length).zip evs).mapM (fun p => parseLine p.1 p.2) = .ok xs)
    {ad : List (Option ID)} (hadd : xs.mapM addedServer = .ok ad) :
    newTraceWith evs pv cq = newTraceTail xs (SetIds.mk (xs.map Line.nid ++ ad.filterMap id)) pv cq := by
  have hne' : evs.isEmpty = false := by simpa using hne
  unfold newTraceWith
  simp only [hne', hlines, hadd, bind, Except.bind, Bool.false_eq_true, ite_false]
  rfl

theorem foldl_bLastF_le (xs : List Line) (i : ID) (N : Nat) :
    ∀ (l : List (Nat × Line)) (acc : Nat), (∀ p ∈ l, p.1 ≤ N) → acc ≤ N → l.foldl (bLastF xs i) acc ≤ N
  | [], _, _, h => h
  | p :: l, acc, hl, h => by
    rw [List.foldl_cons]
    apply foldl_bLastF_le xs i N l _ (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    unfold bLastF; split
    · exact hl p List.mem_cons_self
    · exact h

theorem bootstrapOf_snd_le (xs : List Line) (i : ID) : (bootstrapOf xs i).2 ≤ xs.length := by
  rw [bootstrapOf_eq]
  apply foldl_bLastF_le _ _ _ _ _ _ (Nat.zero_le _)
  intro p hp
  have := bIdx_take_fst_le (j := xs.length) (lines := xs) (p := p)
    (by rw [List.take_of_length_le (by rw [bIdx_length]; exact Nat.le_refl _)]; exact hp)
  exact this

theorem find_map_pair {β : Type} (f : ID → β) : ∀ (l : List ID) (i : ID), i ∈ l →
    (l.map (fun j => (j, f j))).find? (fun p => p.1 == i) = some (i, f i)
  | [], _, h => by simp at h
  | j :: l, i, h => by
    rw [List.map_cons, List.find?_cons]
    by_cases hj : j = i
    · subst hj; simp
    · have : (j == i) = false := by simpa using hj
      simp only [this]
      exact find_map_pair f l i (by rcases List.mem_cons.1 h with h | h; exact absurd h.symm hj; exact h)

theorem tLast_eq (xs : List Line) (srv : SetIds) (i : ID) (hi : i ∈ srv) : tLast xs srv i = (bootstrapOf xs i).2 := by
  unfold tLast tPer; rw [find_map_pair _ srv i hi]; rfl

theorem tPer_find_none (xs : List Line) (srv : SetIds) (h : ∀ j ∈ srv, (bootstrapOf xs j).2 ≠ 0) :
    (tPer xs srv).find? (fun p => p.2.2 == 0) = none := by
  rw [List.find?_eq_none]
  intro p hp
  simp only [tPer, List.mem_map] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  simpa using h j hj

theorem tail_init_err {xs : List Line} {srv : SetIds} (pv cq : Bool) (h : ∀ j ∈ srv, (bootstrapOf xs j).2 ≠ 0)
    (hx : (xs.getD 0 default).nid ∈ srv) {e : TraceError}
    (he : tBC xs (bootstrapOf xs (xs.getD 0 default).nid).2 = .error e) :
    newTraceTail xs srv pv cq = .error e := by
  unfold newTraceTail
  simp only [tPer_find_none xs srv h, tLast_eq xs srv _ hx, he, bind, Except.bind]

theorem tail_sub_err {xs : List Line} {srv : SetIds} (pv cq : Bool) (h : ∀ j ∈ srv, (bootstrapOf xs j).2 ≠ 0)
    (hx : (xs.getD 0 default).nid ∈ srv) {c : SetIds}
    (hc : tBC xs (bootstrapOf xs (xs.getD 0 default).nid).2 = .ok c) (hs : c.subset srv = false) :
    ∃ e, newTraceTail xs srv pv cq = .error e := by
  refine ⟨{ what := "TraceInitServer not a subset of TraceServer", line := 0, n := 0 }, ?_⟩
  unfold newTraceTail
  simp only [tPer_find_none xs srv h, tLast_eq xs srv _ hx, hc, hs, bind, Except.bind, Bool.not_false, ite_true]
  rfl

theorem mapM_take_err {α β ε : Type} (f : α → Except ε β) (l : List α) (m : Nat) (e : ε)
    (h : (l.take m).mapM f = .error e) : l.mapM f = .error e := by
  rw [← List.take_append_drop m l, List.mapM_append, h]; rfl

/-- The configuration function of `newTraceTail`'s `cfgs`. -/
abbrev tCfgF (xs : List Line) (srv : SetIds) : ID → Except TraceError (ID × SetIds) :=
  fun i => do return (i, ← tBC xs (tLast xs srv i))

theorem tail_cfg_err {xs : List Line} {srv : SetIds} (pv cq : Bool) (h : ∀ j ∈ srv, (bootstrapOf xs j).2 ≠ 0)
    (hx : (xs.getD 0 default).nid ∈ srv) {c : SetIds}
    (hc : tBC xs (bootstrapOf xs (xs.getD 0 default).nid).2 = .ok c) (hs : c.subset srv = true)
    {m : Nat} {e : TraceError} (he : (srv.take m).mapM (tCfgF xs srv) = .error e) :
    ∃ e, newTraceTail xs srv pv cq = .error e := by
  refine ⟨e, ?_⟩
  have := mapM_take_err _ _ _ _ he
  unfold newTraceTail
  simp only [tPer_find_none xs srv h, tLast_eq xs srv _ hx, hc, hs, bind, Except.bind, Bool.not_true,
    Bool.false_eq_true, ite_false]
  unfold tCfgF at this; simp only [bind, Except.bind] at this
  rw [this]

theorem tail_conf_err {xs : List Line} {srv : SetIds} (pv cq : Bool) (h : ∀ j ∈ srv, (bootstrapOf xs j).2 ≠ 0)
    (hx : (xs.getD 0 default).nid ∈ srv) {c : SetIds}
    (hc : tBC xs (bootstrapOf xs (xs.getD 0 default).nid).2 = .ok c) (hs : c.subset srv = true)
    {m : Nat} {e : TraceError} (he : (srv.take m).mapM (tBconfF xs srv) = .error e) :
    ∃ e, newTraceTail xs srv pv cq = .error e := by
  cases hcf : srv.mapM (tCfgF xs srv) with
  | error e' =>
    refine ⟨e', ?_⟩
    unfold newTraceTail
    simp only [tPer_find_none xs srv h, tLast_eq xs srv _ hx, hc, hs, bind, Except.bind, Bool.not_true,
      Bool.false_eq_true, ite_false]
    unfold tCfgF at hcf; simp only [bind, Except.bind] at hcf
    rw [hcf]
  | ok cfgs =>
    refine ⟨e, ?_⟩
    have := mapM_take_err _ _ _ _ he
    unfold newTraceTail
    simp only [tPer_find_none xs srv h, tLast_eq xs srv _ hx, hc, hs, bind, Except.bind, Bool.not_true,
      Bool.false_eq_true, ite_false]
    unfold tCfgF at hcf; simp only [bind, Except.bind] at hcf
    rw [hcf]; simp only
    rw [this]

theorem tail_ok {xs : List Line} {srv : SetIds} (pv cq : Bool) (h : ∀ j ∈ srv, (bootstrapOf xs j).2 ≠ 0)
    (hx : (xs.getD 0 default).nid ∈ srv) {c : SetIds}
    (hc : tBC xs (bootstrapOf xs (xs.getD 0 default).nid).2 = .ok c) (hs : c.subset srv = true)
    {cfgs : List (ID × SetIds)} {bconfs : List (ID × List SetIds)}
    (hcf : srv.mapM (tCfgF xs srv) = .ok cfgs) (hbf : srv.mapM (tBconfF xs srv) = .ok bconfs) :
    newTraceTail xs srv pv cq = .ok
      { lines := xs, server := srv, initSrv := c,
        bootstrap := (List.range xs.length).map (fun k => (tPer xs srv).any (fun p => p.2.1.getD k false)),
        init :=
          { server := srv, s := (fun i => tServerOf xs srv cfgs bconfs i), messages := [],
            pendingMessages := [], reconfigCount := 0, preVote := pv, checkQuorum := cq } } := by
  unfold newTraceTail
  simp only [tPer_find_none xs srv h, tLast_eq xs srv _ hx, hc, hs, bind, Except.bind, Bool.not_true,
    Bool.false_eq_true, ite_false]
  unfold tCfgF at hcf; simp only [bind, Except.bind] at hcf
  rw [hcf]; simp only
  rw [hbf]; rfl

theorem mapM_pair_fst {β ε : Type} (g : ID → Except ε (ID × β)) (hg : ∀ i r, g i = .ok r → r.1 = i) :
    ∀ (l : List ID) (r : List (ID × β)), l.mapM g = .ok r → r.map Prod.fst = l
  | [], r, h => by simp [Pure.pure, Except.pure] at h; subst h; rfl
  | i :: l, r, h => by
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    cases hgi : g i with
    | error e => rw [hgi] at h; cases h
    | ok x =>
      rw [hgi] at h
      simp only at h
      cases hl : l.mapM g with
      | error e => rw [hl] at h; cases h
      | ok r' =>
        rw [hl] at h
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [hg i x hgi, mapM_pair_fst g hg l r' hl]

theorem find_append_some {β : Type} {l r : List (ID × β)} {j : ID} (hj : j ∈ l.map Prod.fst) :
    (l ++ r).find? (fun p => p.1 == j) = l.find? (fun p => p.1 == j) := by
  rw [List.find?_append]
  cases h : l.find? (fun p => p.1 == j) with
  | none =>
    rw [List.find?_eq_none] at h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
    exact absurd (by simp) (h p hp)
  | some x => rfl

theorem find_append_none {β : Type} {l : List (ID × β)} {j : ID} (x : β) (hj : j ∉ l.map Prod.fst) :
    (l ++ [(j, x)]).find? (fun p => p.1 == j) = some (j, x) := by
  rw [List.find?_append]
  have : l.find? (fun p => p.1 == j) = none := by
    rw [List.find?_eq_none]
    intro p hp hpj
    exact hj (List.mem_map.2 ⟨p, hp, by simpa using hpj⟩)
  rw [this]; simp

theorem tServerOf_congr (xs : List Line) (srv : SetIds) (cfgs cfgs' : List (ID × SetIds))
    (bconfs bconfs' : List (ID × List SetIds)) (i : ID)
    (hc : cfgs.find? (fun p => p.1 == i) = cfgs'.find? (fun p => p.1 == i))
    (hb : bconfs.find? (fun p => p.1 == i) = bconfs'.find? (fun p => p.1 == i)) :
    tServerOf xs srv cfgs bconfs i = tServerOf xs srv cfgs' bconfs' i := by
  unfold tServerOf; rw [hc, hb]

end Etcdraft
end EtcdGrove
end Perennial
