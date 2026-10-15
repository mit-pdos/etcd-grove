/-
The index's history (`InvIndex.lean`): the events put into the key index, with a commit marker
after each revision (`HistItem`), as the writer records them in a monotone list. `histOf log`
is the history of a committed log, `histShape ilog pend` that of `ilog` committed and `pend` the
pending revision's changes so far. Pure; Lean-first.

The reader's stability lemma (`kiGet_fold_below`): the answer of a key index at a revision
below every later event's main is unchanged by those events; with `histOf_prefix_shape`, a
reader whose certified log `log₀` is a prefix of the index's history reads, at a revision below
`log₀.length`, what `log₀` determines.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LogLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ### The history -/

/-- An item of the index's history: an event put into the index, or the commit of a revision. -/
inductive HistItem where
  | ev (e : Ev)
  | commit
deriving Inhabited

/-- The events of the revisions of `log` numbered from `i`. -/
def evsOfFrom (i : Nat) (log : Log) : List Ev :=
  ((log.zipIdx i).map fun p => evsOfRev p.2 p.1).flatten

theorem evsOf_eq_evsOfFrom (log : Log) : evsOf log = evsOfFrom 0 log := rfl

theorem evsOfFrom_nil (i : Nat) : evsOfFrom i [] = [] := rfl

theorem evsOfFrom_cons (i : Nat) (cs : List Change) (log : Log) :
    evsOfFrom i (cs :: log) = evsOfRev i cs ++ evsOfFrom (i + 1) log := by
  unfold evsOfFrom
  rw [List.zipIdx_cons, List.map_cons, List.flatten_cons]

theorem evsOfFrom_append (i : Nat) (log : Log) (cs : List Change) :
    evsOfFrom i (log ++ [cs]) = evsOfFrom i log ++ evsOfRev (i + log.length) cs := by
  unfold evsOfFrom
  rw [List.zipIdx_append, List.map_append, List.flatten_append]
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil]

/-- Mains of events as numbers: `W64` of a small number. -/
theorem toNat_W64 (n : Nat) (h : n < 2 ^ 63) : (W64 n).toNat = n := by word

/-- The history of the committed log `log`, its revisions numbered from `i`. -/
def histOfFrom : Nat → Log → List HistItem
  | _, [] => []
  | i, cs :: log => (evsOfRev i cs).map .ev ++ [.commit] ++ histOfFrom (i + 1) log

/-- The history of the committed log `log`. -/
def histOf (log : Log) : List HistItem := histOfFrom 0 log

/-- The history of `ilog` committed and the changes `pend` of the pending revision put. -/
def histShape (ilog : Log) (pend : List Change) : List HistItem :=
  histOf ilog ++ (evsOfRev ilog.length pend).map .ev

/-- The events of a history. -/
def evsOfHist (h : List HistItem) : List Ev :=
  h.filterMap fun
    | .ev e => some e
    | .commit => none

theorem evsOfHist_append (h1 h2 : List HistItem) :
    evsOfHist (h1 ++ h2) = evsOfHist h1 ++ evsOfHist h2 := by
  unfold evsOfHist; rw [List.filterMap_append]

theorem evsOfHist_map_ev : ∀ (es : List Ev), evsOfHist (es.map .ev) = es
  | [] => rfl
  | e :: es => by
    show List.filterMap _ (HistItem.ev e :: es.map .ev) = e :: es
    rw [List.filterMap_cons]
    exact congrArg (e :: ·) (evsOfHist_map_ev es)

theorem evsOfHist_commit : evsOfHist [.commit] = [] := rfl

theorem evsOfHist_histOfFrom (i : Nat) : ∀ (log : Log), evsOfHist (histOfFrom i log) = evsOfFrom i log
  | [] => rfl
  | cs :: log => by
    rw [histOfFrom, evsOfFrom_cons, evsOfHist_append, evsOfHist_append, evsOfHist_map_ev,
      evsOfHist_commit, List.append_nil, evsOfHist_histOfFrom (i + 1) log]

theorem evsOfHist_histOf (log : Log) : evsOfHist (histOf log) = evsOf log :=
  evsOfHist_histOfFrom 0 log

theorem evsOfHist_histShape (ilog : Log) (pend : List Change) :
    evsOfHist (histShape ilog pend) = evsOf (ilog ++ [pend]) := by
  unfold histShape
  rw [evsOfHist_append, evsOfHist_histOf, evsOfHist_map_ev, evsOf_append]

theorem histOfFrom_append (i : Nat) : ∀ (log : Log) (cs : List Change),
    histOfFrom i (log ++ [cs]) =
      histOfFrom i log ++ (evsOfRev (i + log.length) cs).map .ev ++ [.commit]
  | [], cs => by simp [histOfFrom]
  | c :: log, cs => by
    rw [List.cons_append, histOfFrom, histOfFrom, histOfFrom_append (i + 1) log cs]
    simp only [List.length_cons, List.append_assoc]
    rw [show i + 1 + log.length = i + (log.length + 1) by omega]

/-- A commit closes the pending revision. -/
theorem histShape_commit (ilog : Log) (pend : List Change) :
    histShape ilog pend ++ [.commit] = histShape (ilog ++ [pend]) [] := by
  unfold histShape histOf
  simp [histOfFrom_append, evsOfRev]

/-- The event of a change appended to the pending revision. -/
def evOfChange (m i : Nat) (c : Change) : Ev :=
  { rev := ⟨W64 m, W64 i⟩, change := c }

theorem evsOfRev_append_singleton (m : Nat) (cs : List Change) (c : Change) :
    evsOfRev m (cs ++ [c]) = evsOfRev m cs ++ [evOfChange m cs.length c] := by
  unfold evsOfRev evOfChange
  rw [List.zipIdx_append, List.map_append]
  simp

theorem histShape_ev (ilog : Log) (pend : List Change) (c : Change) :
    histShape ilog pend ++ [.ev (evOfChange ilog.length pend.length c)] =
      histShape ilog (pend ++ [c]) := by
  unfold histShape
  rw [evsOfRev_append_singleton, List.map_append, List.map_cons, List.map_nil, List.append_assoc]

theorem evCount_histShape (ilog : Log) (pend : List Change) :
    (evsOfHist (histShape ilog pend)).length = (evsOf (ilog ++ [pend])).length := by
  rw [evsOfHist_histShape]

/-! ### A reader's certified log, as a prefix of the history -/

/-- The events of `l`, numbered from `i`, have mains in `[i, i + l.length)`, nondecreasing. -/
theorem evsOfRev_main (m : Nat) (cs : List Change) : ∀ e ∈ evsOfRev m cs, e.rev.main = W64 m := by
  unfold evsOfRev
  intro e he
  rw [List.mem_map] at he
  obtain ⟨p, -, rfl⟩ := he
  rfl

theorem evsOfRev_sub (m : Nat) (cs : List Change) :
    ∀ (j : Nat) (e : Ev), (evsOfRev m cs)[j]? = some e → e.rev.sub = W64 j ∧ j < cs.length := by
  unfold evsOfRev
  intro j e he
  rw [List.getElem?_map] at he
  cases hz : (cs.zipIdx)[j]? with
  | none => rw [hz] at he; simp at he
  | some p =>
    rw [hz] at he
    simp only [Option.map_some, Option.some.injEq] at he
    have hj : j < cs.zipIdx.length := (List.getElem?_eq_some_iff.1 hz).1
    rw [List.length_zipIdx] at hj
    have := List.getElem_zipIdx (l := cs) (j := 0) (i := j) (by rw [List.length_zipIdx]; exact hj)
    rw [List.getElem?_eq_getElem (by rw [List.length_zipIdx]; exact hj), this] at hz
    simp only [Option.some.injEq] at hz
    subst hz
    rw [← he]
    exact ⟨by simp, hj⟩

theorem evsOfFrom_main (i : Nat) : ∀ (log : Log) (e : Ev), e ∈ evsOfFrom i log →
    ∃ j, j < log.length ∧ e.rev.main = W64 (i + j)
  | [], e, he => by simp [evsOfFrom_nil] at he
  | cs :: log, e, he => by
    rw [evsOfFrom_cons, List.mem_append] at he
    rcases he with he | he
    · exact ⟨0, by simp, by have := evsOfRev_main i cs e he; rw [this]; simp⟩
    · obtain ⟨j, hj, he⟩ := evsOfFrom_main (i + 1) log e he
      exact ⟨j + 1, by simp; omega, by rw [he]; congr 1; omega⟩

/-- Events whose mains are at least `b`, nondecreasing, below `2^63`. -/
structure EvsFrom (b : Nat) (es : List Ev) : Prop where
  ge : ∀ e ∈ es, b ≤ e.rev.main.toNat
  lt : ∀ e ∈ es, e.rev.main.toNat < 2 ^ 63
  sorted : es.Pairwise fun a c => a.rev.main.toNat ≤ c.rev.main.toNat

theorem EvsFrom.nil (b : Nat) : EvsFrom b [] :=
  ⟨fun _ h => by simp at h, fun _ h => by simp at h, List.Pairwise.nil⟩

theorem EvsFrom.mono {b b' : Nat} {es : List Ev} (h : EvsFrom b es) (hb : b' ≤ b) : EvsFrom b' es :=
  ⟨fun e he => Nat.le_trans hb (h.ge e he), h.lt, h.sorted⟩

theorem EvsFrom.append {b : Nat} {es1 es2 : List Ev} (h1 : EvsFrom b es1) (h2 : EvsFrom b es2)
    (hsep : ∀ e1 ∈ es1, ∀ e2 ∈ es2, e1.rev.main.toNat ≤ e2.rev.main.toNat) : EvsFrom b (es1 ++ es2) :=
  ⟨fun e he => by
      rcases List.mem_append.1 he with he | he
      · exact h1.ge e he
      · exact h2.ge e he,
   fun e he => by
      rcases List.mem_append.1 he with he | he
      · exact h1.lt e he
      · exact h2.lt e he,
   List.pairwise_append.2 ⟨h1.sorted, h2.sorted, hsep⟩⟩

theorem EvsFrom.evsOfRev (m : Nat) (hm : m < 2 ^ 63) (cs : List Change) : EvsFrom m (evsOfRev m cs) :=
  ⟨fun e he => by rw [evsOfRev_main m cs e he]; word,
   fun e he => by rw [evsOfRev_main m cs e he]; word,
   List.pairwise_of_forall_mem_list fun a ha c hc => by
      rw [evsOfRev_main m cs a ha, evsOfRev_main m cs c hc]; exact Nat.le_refl _⟩

theorem EvsFrom.evsOfFrom (i : Nat) : ∀ (log : Log), i + log.length < 2 ^ 63 →
    EvsFrom i (evsOfFrom i log)
  | [], _ => by rw [evsOfFrom_nil]; exact EvsFrom.nil i
  | cs :: log, hlen => by
    rw [evsOfFrom_cons]
    simp only [List.length_cons] at hlen
    refine EvsFrom.append (EvsFrom.evsOfRev i (by omega) cs)
      ((EvsFrom.evsOfFrom (i + 1) log (by omega)).mono (Nat.le_succ i)) ?_
    intro e1 he1 e2 he2
    rw [evsOfRev_main i cs e1 he1]
    obtain ⟨j, hj, he2⟩ := evsOfFrom_main (i + 1) log e2 he2
    rw [he2]
    have : i + 1 + j < 2 ^ 63 := by omega
    word

/-- No item of a history's event part is a commit. -/
theorem map_ev_ne_commit (es : List Ev) : ∀ x ∈ es.map HistItem.ev, x ≠ .commit := by
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨e, -, rfl⟩ := hx
  exact HistItem.noConfusion

/-- A prefix relation between two histories whose first commits delimit event parts: the event
parts agree and the rest is a prefix. -/
theorem prefix_commit_split : ∀ (A B : List HistItem) (X Y : List HistItem),
    (∀ x ∈ A, x ≠ HistItem.commit) → (∀ x ∈ B, x ≠ HistItem.commit) →
    A ++ [HistItem.commit] ++ X <+: B ++ [HistItem.commit] ++ Y → A = B ∧ X <+: Y
  | [], [], X, Y, _, _, h => ⟨rfl, (List.cons_prefix_cons.1 h).2⟩
  | [], b :: B, X, Y, _, hB, h => by
    simp only [List.nil_append, List.cons_append, List.cons_prefix_cons] at h
    exact absurd h.1.symm (hB b List.mem_cons_self)
  | a :: A, [], X, Y, hA, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons_prefix_cons] at h
    exact absurd h.1 (hA a List.mem_cons_self)
  | a :: A, b :: B, X, Y, hA, hB, h => by
    simp only [List.cons_append, List.cons_prefix_cons] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨hAB, hXY⟩ := prefix_commit_split A B X Y (fun x hx => hA x (List.mem_cons_of_mem _ hx))
      (fun x hx => hB x (List.mem_cons_of_mem _ hx)) h
    exact ⟨by rw [hAB], hXY⟩

theorem map_ev_injective : ∀ (es1 es2 : List Ev), es1.map HistItem.ev = es2.map HistItem.ev →
    es1 = es2
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | e :: es1, e' :: es2, h => by
    simp only [List.map_cons, List.cons.injEq, HistItem.ev.injEq] at h
    rw [h.1, map_ev_injective es1 es2 h.2]

/-- A certified log's history as a prefix of the index's history: the index's events are the
log's followed by events of later revisions (nondecreasing mains, from the log's length). -/
theorem histOfFrom_prefix (i : Nat) : ∀ (log ilog : Log) (pend : List Change),
    histOfFrom i log <+: histOfFrom i ilog ++ (evsOfRev (i + ilog.length) pend).map .ev →
    i + ilog.length < 2 ^ 63 →
    ∃ rest, evsOfHist (histOfFrom i ilog ++ (evsOfRev (i + ilog.length) pend).map .ev) =
      evsOfFrom i log ++ rest ∧ EvsFrom (i + log.length) rest ∧ log.length ≤ ilog.length
  | [], ilog, pend, _, hlen => by
    refine ⟨_, by rw [evsOfFrom_nil, List.nil_append], ?_, by simp⟩
    rw [evsOfHist_append, evsOfHist_histOfFrom, evsOfHist_map_ev, List.length_nil, Nat.add_zero]
    refine EvsFrom.append (EvsFrom.evsOfFrom i ilog hlen)
      ((EvsFrom.evsOfRev (i + ilog.length) hlen pend).mono (by omega)) ?_
    intro e1 he1 e2 he2
    obtain ⟨j, hj, he1⟩ := evsOfFrom_main i ilog e1 he1
    rw [he1, evsOfRev_main _ _ e2 he2]
    word
  | c :: log, ilog, pend, hpre, hlen => by
    cases ilog with
    | nil =>
      exfalso
      rw [histOfFrom, histOfFrom, List.nil_append] at hpre
      obtain ⟨R, hR⟩ := hpre
      have : HistItem.commit ∈ (evsOfRev (i + ([] : Log).length) pend).map HistItem.ev := by
        rw [← hR]; simp
      exact map_ev_ne_commit _ _ this rfl
    | cons c' ilog =>
      rw [histOfFrom, histOfFrom] at hpre
      simp only [List.length_cons] at hpre hlen ⊢
      rw [List.append_assoc ((evsOfRev i c').map HistItem.ev ++ [HistItem.commit])
        (histOfFrom (i + 1) ilog)] at hpre
      obtain ⟨hcc, hpre'⟩ := prefix_commit_split _ _ _ _ (map_ev_ne_commit _) (map_ev_ne_commit _)
        hpre
      have hc : evsOfRev i c = evsOfRev i c' := map_ev_injective _ _ hcc
      rw [show i + (ilog.length + 1) = i + 1 + ilog.length by omega] at hpre' hlen ⊢
      obtain ⟨rest, hrest, hfrom, hle⟩ := histOfFrom_prefix (i + 1) log ilog pend hpre' hlen
      refine ⟨rest, ?_, ?_, by omega⟩
      · rw [histOfFrom, List.append_assoc, List.append_assoc, evsOfHist_append, evsOfHist_map_ev,
          evsOfHist_append, evsOfHist_commit, List.nil_append, hrest, evsOfFrom_cons, hc,
          List.append_assoc]
      · rw [show i + (log.length + 1) = i + 1 + log.length by omega]; exact hfrom

/-- `histOfFrom_prefix` for a certified log `log` and the index's history `histShape ilog pend`. -/
theorem histOf_prefix_shape (log ilog : Log) (pend : List Change)
    (hpre : histOf log <+: histShape ilog pend) (hlen : ilog.length < 2 ^ 63) :
    ∃ rest, evsOf (ilog ++ [pend]) = evsOf log ++ rest ∧ EvsFrom log.length rest ∧
      log.length ≤ ilog.length := by
  unfold histOf histShape at hpre
  rw [show ilog.length = 0 + ilog.length by omega] at hpre
  obtain ⟨rest, hrest, hfrom, hle⟩ := histOfFrom_prefix 0 log ilog pend hpre (by omega)
  refine ⟨rest, ?_, by rw [Nat.zero_add] at hfrom; exact hfrom, hle⟩
  rw [← evsOfHist_histShape]
  unfold histShape histOf
  rw [show ilog.length = 0 + ilog.length by omega, hrest, evsOf_eq_evsOfFrom]

/-! ### The history determines the log -/

/-- The changes of a revision's events are the revision's changes. -/
theorem evsOfRev_change (m : Nat) (cs : List Change) : (evsOfRev m cs).map Ev.change = cs := by
  unfold evsOfRev
  rw [List.map_map]
  show List.map (fun p => p.1) cs.zipIdx = cs
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.zipIdx_cons, List.map_cons]
    congr 1
    rw [List.zipIdx_succ, List.map_map]
    exact ih

/-- **The history of a committed log determines it**: a prefix of histories is a prefix of
logs (the commits delimit the revisions, and the events carry the changes). -/
theorem histOfFrom_prefix_log (i : Nat) : ∀ (L1 L2 : Log),
    histOfFrom i L1 <+: histOfFrom i L2 → L1 <+: L2
  | [], _, _ => List.nil_prefix
  | c :: L1, [], h => by
    exfalso
    rw [histOfFrom, histOfFrom] at h
    have := h.length_le
    simp at this
  | c :: L1, c' :: L2, h => by
    rw [histOfFrom, histOfFrom] at h
    simp only [List.append_assoc] at h
    obtain ⟨hcc, h'⟩ := prefix_commit_split _ _ _ _ (map_ev_ne_commit _) (map_ev_ne_commit _)
      (by simpa only [List.append_assoc] using h)
    have hc := congrArg (List.map Ev.change) (map_ev_injective _ _ hcc)
    rw [evsOfRev_change, evsOfRev_change] at hc
    subst hc
    exact List.cons_prefix_cons.2 ⟨rfl, histOfFrom_prefix_log (i + 1) L1 L2 h'⟩

theorem histOf_prefix_log {L1 L2 : Log} (h : histOf L1 <+: histOf L2) : L1 <+: L2 :=
  histOfFrom_prefix_log 0 L1 L2 h

/-- Two lower bounds of one history (comparable): their logs are comparable. -/
theorem histOf_cmp_log {L1 L2 : Log} (h : histOf L1 <+: histOf L2 ∨ histOf L2 <+: histOf L1) :
    L1 <+: L2 ∨ L2 <+: L1 :=
  h.imp histOf_prefix_log histOf_prefix_log

theorem histOf_inj {L1 L2 : Log} (h : histOf L1 = histOf L2) : L1 = L2 := by
  have h1 : L1 <+: L2 := histOf_prefix_log (by rw [h]; exact List.prefix_refl _)
  have h2 : L2 <+: L1 := histOf_prefix_log (by rw [h]; exact List.prefix_refl _)
  exact h1.eq_of_length (Nat.le_antisymm h1.length_le h2.length_le)

/-- A committed log's history below the writer's (`histShape ilog pend`, no commit after
`pend`): the log is a prefix of the committed part `ilog`. -/
theorem histOfFrom_prefix_shape_log (i : Nat) : ∀ (L ilog : Log) (E : List HistItem),
    (∀ x ∈ E, x ≠ HistItem.commit) → histOfFrom i L <+: histOfFrom i ilog ++ E → L <+: ilog
  | [], _, _, _, _ => List.nil_prefix
  | c :: L, [], E, hE, h => by
    exfalso
    rw [histOfFrom, histOfFrom, List.nil_append] at h
    obtain ⟨R, hR⟩ := h
    have : HistItem.commit ∈ E := by rw [← hR]; simp
    exact hE _ this rfl
  | c :: L, c' :: ilog, E, hE, h => by
    rw [histOfFrom, histOfFrom] at h
    obtain ⟨hcc, h'⟩ := prefix_commit_split _ _ _ _ (map_ev_ne_commit _) (map_ev_ne_commit _)
      (by simpa only [List.append_assoc] using h)
    have hc := congrArg (List.map Ev.change) (map_ev_injective _ _ hcc)
    rw [evsOfRev_change, evsOfRev_change] at hc
    subst hc
    exact List.cons_prefix_cons.2 ⟨rfl, histOfFrom_prefix_shape_log (i + 1) L ilog E hE h'⟩

theorem histOf_prefix_shape_log {L ilog : Log} {pend : List Change}
    (h : histOf L <+: histShape ilog pend) : L <+: ilog :=
  histOfFrom_prefix_shape_log 0 L ilog _ (map_ev_ne_commit _) h

/-- The writer's history after the commit marker of its pending revision is the history of the
log with that revision committed. -/
theorem histShape_seal (ilog : Log) (pend : List Change) :
    histShape ilog pend ++ [.commit] = histOf (ilog ++ [pend]) := by
  rw [histShape_commit]; simp [histShape, evsOfRev]

/-- The events of a history that is a prefix of a certified log's, with as many events: the
log's events. -/
theorem evsOfHist_prefix_of_count (h : List HistItem) (log : Log) (hpre : h <+: histOf log)
    (hcount : (evsOf log).length ≤ (evsOfHist h).length) : evsOfHist h = evsOf log := by
  obtain ⟨T, hT⟩ := hpre
  have := evsOfHist_histOf log
  rw [← hT, evsOfHist_append] at this
  rw [← this] at hcount ⊢
  rw [List.length_append] at hcount
  have hnil : evsOfHist T = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [hnil, List.append_nil]

/-- Two histories, one a prefix of the other, with as many events: the same events. -/
theorem evsOfHist_prefix_eq (h1 h2 : List HistItem) (hpre : h1 <+: h2)
    (hc : (evsOfHist h2).length ≤ (evsOfHist h1).length) : evsOfHist h1 = evsOfHist h2 := by
  obtain ⟨T, hT⟩ := hpre
  rw [← hT, evsOfHist_append] at hc ⊢
  rw [List.length_append] at hc
  have hnil : evsOfHist T = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [hnil, List.append_nil]

/-- The events of the pending revision's next change. -/
theorem evsOf_append_change (ilog : Log) (pend : List Change) (c : Change) :
    evsOf (ilog ++ [pend ++ [c]]) = evsOf (ilog ++ [pend]) ++ [evOfChange ilog.length pend.length c] := by
  rw [evsOf_append, evsOf_append, evsOfRev_append_singleton, List.append_assoc]

theorem indexOf_append_ev (evs : List Ev) (ev : Ev) :
    indexOf (evs ++ [ev]) = idxApply (indexOf evs) ev := by
  unfold indexOf; rw [List.foldl_append]; rfl

theorem evOfChange_put (m i : Nat) (k v : GoString) (l : w64) :
    evOfChange m i (.put k v l) = { rev := ⟨W64 m, W64 i⟩, change := .put k v l } := rfl

theorem evOfChange_del (m i : Nat) (k : GoString) :
    evOfChange m i (.del k) = { rev := ⟨W64 m, W64 i⟩, change := .del k } := rfl

/-! ### A reader's answer is stable under later events -/

theorem kiFold_cons (ki : KeyIndex) (e : Ev) (es : List Ev) (k : GoString) :
    kiFold ki (e :: es) k = kiFold (if e.key = k then kiApply ki e else ki) es k := by
  unfold kiFold
  rw [List.filter_cons]
  by_cases h : e.key = k
  · simp [h]
  · simp [h]

theorem kiApply_wf {ki : KeyIndex} (hwf : KiWf ki) (e : Ev) : KiWf (kiApply ki e) := by
  unfold kiApply
  split
  · split
    · exact hwf
    · exact hwf.tombstone _
  · exact hwf.put _

theorem kiApply_revs {ki : KeyIndex} (hwf : KiWf ki) (e : Ev) :
    ∀ r ∈ kiRevs (kiApply ki e), r ∈ kiRevs ki ∨ r = e.rev := by
  unfold kiApply
  intro r hr
  split at hr
  · split at hr
    · exact Or.inl hr
    · rw [kiRevs_kiTombstone hwf.ne, List.mem_append, List.mem_singleton] at hr; exact hr
  · rw [kiRevs_kiPut hwf.ne, List.mem_append, List.mem_singleton] at hr; exact hr

theorem kiGet_kiApply_below {ki : KeyIndex} (hwf : KiWf ki) {b : Nat} (hb : b < 2 ^ 63)
    (hrevs : ∀ rev ∈ kiRevs ki, rev.main.toNat ≤ b) (e : Ev) (he : b ≤ e.rev.main.toNat)
    (he2 : e.rev.main.toNat < 2 ^ 63) {r : Nat} (hr : r < b) :
    kiGet (kiApply ki e) (W64 r) = kiGet ki (W64 r) := by
  have habove : KiAbove ki e.rev := by
    intro x hx; have := hrevs x hx; word
  unfold kiApply
  split
  · split
    · rfl
    · exact kiGet_kiTombstone_below hwf habove (by word)
  · exact kiGet_kiPut_below hwf habove (by word)

/-- Events at or above `b` (nondecreasing) do not change a key index's answer below `b`. -/
theorem kiGet_fold_below (k : GoString) : ∀ (es : List Ev) (ki : KeyIndex) (b : Nat), KiWf ki →
    (∀ rev ∈ kiRevs ki, rev.main.toNat ≤ b) → b < 2 ^ 63 → EvsFrom b es →
    ∀ r : Nat, r < b → kiGet (kiFold ki es k) (W64 r) = kiGet ki (W64 r)
  | [], ki, b, _, _, _, _, r, _ => rfl
  | e :: es, ki, b, hwf, hrevs, hb, hes, r, hr => by
    rw [kiFold_cons]
    have hge := hes.ge e List.mem_cons_self
    have hlt := hes.lt e List.mem_cons_self
    have hsorted := List.pairwise_cons.1 hes.sorted
    have hes' : EvsFrom e.rev.main.toNat es :=
      ⟨fun x hx => hsorted.1 x hx, fun x hx => hes.lt x (List.mem_cons_of_mem _ hx), hsorted.2⟩
    by_cases hk : e.key = k
    · rw [ite_eq_left hk]
      have hrevs' : ∀ x ∈ kiRevs (kiApply ki e), x.main.toNat ≤ e.rev.main.toNat := by
        intro x hx
        rcases kiApply_revs hwf e x hx with hx | hx
        · exact Nat.le_trans (hrevs x hx) hge
        · rw [hx]; exact Nat.le_refl _
      rw [kiGet_fold_below k es (kiApply ki e) e.rev.main.toNat (kiApply_wf hwf e) hrevs' hlt hes' r
        (by omega)]
      exact kiGet_kiApply_below hwf hb hrevs e hge hlt hr
    · rw [ite_eq_right hk]
      exact kiGet_fold_below k es ki e.rev.main.toNat hwf
        (fun x hx => Nat.le_trans (hrevs x hx) hge) hlt hes' r (by omega)

/-- **A reader's answer.** The index holds the events of `ilog ++ [pend]`; a reader with a
certified prefix `log` (well-formed, bounded) reads at `r < log.length` what `log` determines. -/
theorem kiGet_reader (log ilog : Log) (pend : List Change) (hpre : histOf log <+: histShape ilog pend)
    (hlen : ilog.length < 2 ^ 63) (hwf : LogWf' log) (hcs : ∀ cs ∈ log, cs.length < 2 ^ 63)
    (k : GoString) (r : Nat) (hr : r < log.length) :
    kiGet (kiOfKey (evsOf (ilog ++ [pend])) k) (W64 r) = kiGet (kiOfKey (evsOf log) k) (W64 r) := by
  obtain ⟨rest, hrest, hfrom, hle⟩ := histOf_prefix_shape log ilog pend hpre hlen
  rw [hrest, kiOfKey_eq_kiFold, kiFold_append, ← kiOfKey_eq_kiFold]
  have hlink := keyLink_of_rev k log.reverse (by simp; omega)
    (fun cs hcs' => hcs cs (List.mem_reverse.1 hcs')) (by rw [List.reverse_reverse]; exact hwf)
  rw [List.reverse_reverse] at hlink
  exact kiGet_fold_below k rest _ log.length hlink.wf (fun x hx => Nat.le_of_lt (hlink.revs x hx))
    (by omega) hfrom r hr

/-! ### The writer: the key's index is not empty, its `modified` is below the new revision -/

theorem kiApply_modified (ki : KeyIndex) (e : Ev) :
    (kiApply ki e).modified = ki.modified ∨ (kiApply ki e).modified = e.rev := by
  unfold kiApply
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr (kiTombstone_modified _ _)
  · exact Or.inr (kiPut_modified _ _)

theorem kiFold_modified_lt (k : GoString) (rev : Rev) : ∀ (es : List Ev) (ki : KeyIndex),
    Rev.lt ki.modified rev → (∀ e ∈ es, Rev.lt e.rev rev) → Rev.lt (kiFold ki es k).modified rev
  | [], ki, h, _ => h
  | e :: es, ki, h, hes => by
    rw [kiFold_cons]
    apply kiFold_modified_lt k rev es _ _ (fun x hx => hes x (List.mem_cons_of_mem _ hx))
    split
    · rcases kiApply_modified ki e with hm | hm
      · rw [hm]; exact h
      · rw [hm]; exact hes e List.mem_cons_self
    · exact h

/-- Every event of `ilog ++ [pend]` is below the next change's revision `(ilog.length, pend.length)`. -/
theorem evsOf_rev_lt (ilog : Log) (pend : List Change) (hlen : ilog.length < 2 ^ 63)
    (hpend : pend.length < 2 ^ 63) :
    ∀ e ∈ evsOf (ilog ++ [pend]), Rev.lt e.rev ⟨W64 ilog.length, W64 pend.length⟩ := by
  intro e he
  rw [evsOf_append, List.mem_append] at he
  rcases he with he | he
  · obtain ⟨j, hj, hm⟩ := evsOfFrom_main 0 ilog e he
    left
    rw [hm]; simp only; word
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 he
    obtain ⟨hsub, hjl⟩ := evsOfRev_sub _ _ j e hj
    right
    refine ⟨evsOfRev_main _ _ e he, ?_⟩
    rw [hsub]; simp only; word

theorem Rev.lt_zero_of_pos (m s : Nat) (h0 : 1 ≤ m) (hm : m < 2 ^ 63) :
    Rev.lt Rev.zero ⟨W64 m, W64 s⟩ := by
  left; unfold Rev.zero; simp only; word

/-- A key's index is the empty one or its first generation has a revision. -/
def KiHead (ki : KeyIndex) : Prop := ki = kiEmpty ∨ (ki.gens.headD Gen.empty).revs ≠ []

theorem headD_dropLast_append {α : Type} (l : List α) (x d : α) :
    (l.dropLast ++ [x]).headD d = if l.length ≤ 1 then x else l.headD d := by
  cases l with
  | nil => rfl
  | cons a t =>
    cases t with
    | nil => rfl
    | cons b t => rfl

theorem kiPut_head {ki : KeyIndex} (h : KiHead ki) (rev : Rev) :
    ((kiPut ki rev).gens.headD Gen.empty).revs ≠ [] := by
  rw [kiPut_gens, headD_dropLast_append]
  rcases h with h | h
  · subst h
    have h1 : gensOrEmpty ([Gen.empty] : List Gen) = [Gen.empty] := rfl
    simp only [kiEmpty, h1, List.length_singleton, Nat.le_refl, ↓reduceIte]
    have hlast : ([Gen.empty].getLastD Gen.empty) = Gen.empty := rfl
    rw [hlast, genPut_revs]
    simp
  · have hne : ki.gens ≠ [] := by
      intro he; rw [he] at h; exact h rfl
    rw [gensOrEmpty_eq_of_ne hne]
    split
    · rename_i hl
      have : ki.gens.length = 1 := by have := List.length_pos_iff.2 hne; omega
      obtain ⟨g, hg⟩ : ∃ g, ki.gens = [g] := List.length_eq_one_iff.1 this
      rw [hg]
      have hlast : ([g].getLastD Gen.empty) = g := rfl
      rw [hlast, genPut_revs]
      simp
    · exact h

theorem kiPut_gens_ne_nil (ki : KeyIndex) (rev : Rev) : (kiPut ki rev).gens ≠ [] := by
  rw [kiPut_gens]; simp

theorem KiHead.put {ki : KeyIndex} (h : KiHead ki) (rev : Rev) : KiHead (kiPut ki rev) :=
  Or.inr (kiPut_head h rev)

theorem KiHead.apply {ki : KeyIndex} (h : KiHead ki) (e : Ev) : KiHead (kiApply ki e) := by
  unfold kiApply
  split
  · split
    · exact h
    · right
      rw [kiTombstone_gens]
      have hh := kiPut_head h e.rev
      cases hg : (kiPut ki e.rev).gens with
      | nil => exact absurd hg (kiPut_gens_ne_nil ki e.rev)
      | cons g t =>
        rw [hg] at hh
        simpa using hh
  · exact h.put _

theorem KiHead.fold (k : GoString) : ∀ (es : List Ev) (ki : KeyIndex), KiHead ki →
    KiHead (kiFold ki es k)
  | [], ki, h => h
  | e :: es, ki, h => by
    rw [kiFold_cons]
    apply KiHead.fold k es
    split
    · exact h.apply e
    · exact h

theorem KiHead.kiOfKey (evs : List Ev) (k : GoString) : KiHead (kiOfKey evs k) :=
  KiHead.fold k evs kiEmpty (Or.inl rfl)

/-- A key index whose first generation has a revision is not `isEmpty`, and has a generation. -/
theorem kiIsEmpty_false_of_head {ki : KeyIndex} (h : (ki.gens.headD Gen.empty).revs ≠ []) :
    kiIsEmpty ki = false ∧ ki.gens ≠ [] := by
  unfold kiIsEmpty
  cases hg : ki.gens with
  | nil => rw [hg] at h; exact absurd rfl h
  | cons g t =>
    rw [hg] at h
    simp only [List.headD_cons] at h
    cases t with
    | nil => simp [h]
    | cons g' t => simp

/-- A delete the log allows (`LogWf'`: the key is present) finds a key index whose last
generation is not empty. -/
theorem kiLastEmpty_false_of_del (ilog : Log) (pend : List Change) (k : GoString)
    (hwf : LogWf' (ilog ++ [pend])) (hwf' : LogWf' (ilog ++ [pend ++ [.del k]]))
    (hlen : ilog.length + 1 < 2 ^ 63) (hilog : 1 ≤ ilog.length) (hpend : pend.length < 2 ^ 63)
    (hcs : ∀ cs ∈ ilog, cs.length < 2 ^ 63) :
    kiLastEmpty (kiOfKey (evsOf (ilog ++ [pend])) k) = false := by
  have hlink := keyLink_of_rev k (ilog ++ [pend]).reverse (by simp; omega)
    (fun cs hcs' => by
      rcases List.mem_append.1 (List.mem_reverse.1 hcs') with h | h
      · exact hcs cs h
      · rw [List.mem_singleton] at h; rw [h]; exact hpend)
    (by rw [List.reverse_reverse]; exact hwf)
  rw [List.reverse_reverse] at hlink
  -- the key is present after `pend`
  have hpresent := hwf'.2 ilog.length (pend ++ [.del k]) pend.length k
    (by rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl)
    (by rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl)
  rw [List.take_left, stateAt_append_lt _ _ (by omega), stateAt_last, ← stateAfter_append,
    ← stateAt_last] at hpresent
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel] at hpresent
  -- `kiGet` at the top
  have htop := hlink.match_ ilog.length (by omega)
  have habove : KiAbove (kiOfKey (evsOf (ilog ++ [pend])) k) ⟨W64 ilog.length, W64 0⟩ := by
    intro x hx
    have := hlink.revs x hx
    simp only [List.length_append, List.length_singleton] at this
    simp only; word
  rw [kiGet_top hlink.wf habove] at htop
  unfold kiLastEmpty
  by_cases he : ((kiOfKey (evsOf (ilog ++ [pend])) k).gens.getLastD Gen.empty).revs = []
  · rw [ite_eq_left he] at htop
    rw [KvMatch_none_left htop] at hpresent
    simp at hpresent
  · simp only [he, decide_false]

/-! ### Finding a key in a sorted index -/

/-- `btFind` on a list strictly sorted by a key projection: the element with the key. -/
theorem btFind_sorted_eq_find? {V : Type} (keyf : V → GoString) (less : V → V → Prop)
    [DecidableRel less] (hless : ∀ a b, less a b ↔ go.GoStringLt (keyf a) (keyf b)) :
    ∀ (l : List V), (l.map keyf).Pairwise go.GoStringLt → ∀ (x : V),
      btFind less x l = l.find? (fun y => decide (keyf y = keyf x))
  | [], _, _ => rfl
  | w :: ws, hs, x => by
    rw [List.map_cons, List.pairwise_cons] at hs
    unfold btFind
    rw [List.find?_cons]
    by_cases h1 : less w x
    · rw [ite_eq_left h1, btFind_sorted_eq_find? keyf less hless ws hs.2 x]
      have : keyf w ≠ keyf x := fun e => goStringLt_irrefl _ (e ▸ (hless _ _).1 h1)
      simp [this]
    · rw [ite_eq_right h1]
      by_cases h2 : less x w
      · rw [ite_eq_left h2]
        have : keyf w ≠ keyf x := fun e => goStringLt_irrefl _ (e ▸ (hless _ _).1 h2)
        simp only [this, decide_false]
        rw [List.find?_eq_none.2]
        intro y hy
        simp only [decide_eq_true_eq]
        intro e
        have := hs.1 (keyf y) (List.mem_map_of_mem hy)
        rw [e] at this
        exact goStringLt_irrefl _ (goStringLt_trans ((hless _ _).1 h2) this)
      · rw [ite_eq_right h2]
        have : keyf w = keyf x :=
          goStringLt_eq_of_not_lt (fun h => h1 ((hless _ _).2 h)) (fun h => h2 ((hless _ _).2 h))
        simp [this]

theorem idxGet_eq_find? (idx : IndexM) (hs : idx.Pairwise idxLess) (k : GoString) :
    idxGet idx k = (idx.find? fun z => decide (z.1 = k)).map Prod.snd := by
  unfold idxGet
  rw [btFind_sorted_eq_find? Prod.fst idxLess (fun _ _ => Iff.rfl) idx
    (by rw [List.pairwise_map]; exact hs)]

/-- Every key index in the index built from events has a revision in its first generation. -/
theorem indexOf_head (evs : List Ev) : ∀ (pre : List Ev) (idx : IndexM), IdxRep pre idx →
    (∀ z ∈ idx, (z.2.gens.headD Gen.empty).revs ≠ []) →
    ∀ z ∈ evs.foldl idxApply idx, (z.2.gens.headD Gen.empty).revs ≠ [] := by
  induction evs with
  | nil => intro pre idx _ h; exact h
  | cons ev evs ih =>
    intro pre idx hrep h
    rw [List.foldl_cons]
    apply ih (pre ++ [ev]) _ (hrep.step ev)
    intro z hz
    have hki0 : KiHead ((idxGet idx ev.key).getD kiEmpty) := by
      cases hg : idxGet idx ev.key with
      | none => exact Or.inl rfl
      | some ki =>
        right
        unfold idxGet at hg
        cases hf : btFind idxLess (ev.key, KeyIndex.fresh) idx with
        | none => rw [hf] at hg; simp at hg
        | some z' =>
          rw [hf] at hg
          simp only [Option.map_some, Option.some.injEq] at hg
          subst hg
          exact h z' (btFind_mem hf)
    unfold idxApply at hz
    split at hz
    · rw [idxTombstone_eq] at hz
      split at hz
      · exact h z hz
      · rcases btInsert_mem hz with hz | hz
        · subst hz
          simp only
          rw [kiTombstone_gens]
          have hh := kiPut_head hki0 ev.rev
          cases hg : (kiPut ((idxGet idx ev.key).getD kiEmpty) ev.rev).gens with
          | nil => exact absurd hg (kiPut_gens_ne_nil _ _)
          | cons g t => rw [hg] at hh; simpa using hh
        · exact h z hz
    · rw [idxPut_eq] at hz
      rcases btInsert_mem hz with hz | hz
      · subst hz
        exact kiPut_head hki0 ev.rev
      · exact h z hz

theorem indexOf_head' (evs : List Ev) : ∀ z ∈ indexOf evs, (z.2.gens.headD Gen.empty).revs ≠ [] :=
  indexOf_head evs [] [] IdxRep.nil (fun _ h => by simp at h)

theorem indexOf_sorted (evs : List Ev) : (indexOf evs).Pairwise idxLess := (indexOf_rep evs).1

/-! ### The tree's entries: finding and inserting by key -/

/-- An entry of the index: the key index's pointer, its key and its model (`InvIndex.lean`). -/
abbrev IdxEntry := Loc × GoString × KeyIndex

def idxOfEntries (L : List IdxEntry) : IndexM := L.map fun z => (z.2.1, z.2.2)

def itemsOfEntries (L : List IdxEntry) : List (Loc × GoString) := L.map fun z => (z.1, z.2.1)

/-- The items' order: by key (`keyIndex.Less`). -/
def kiItemLess (a b : Loc × GoString) : Prop := go.GoStringLt a.2 b.2

instance kiItemLess_dec : DecidableRel kiItemLess := fun a b => go.goStringLt_dec a.2 b.2

/-- The entries' order: by key. -/
def entryLess (a b : IdxEntry) : Prop := go.GoStringLt a.2.1 b.2.1

instance entryLess_dec : DecidableRel entryLess := fun a b => go.goStringLt_dec a.2.1 b.2.1

theorem idxOfEntries_sorted {L : List IdxEntry} (h : (itemsOfEntries L).Pairwise kiItemLess) :
    (idxOfEntries L).Pairwise idxLess := by
  unfold itemsOfEntries at h
  unfold idxOfEntries
  rw [List.pairwise_map] at h ⊢
  exact h

theorem btFind_items (L : List IdxEntry) (hs : (itemsOfEntries L).Pairwise kiItemLess) (q : Loc)
    (k : GoString) :
    btFind kiItemLess (q, k) (itemsOfEntries L) =
      (L.find? fun z => decide (z.2.1 = k)).map fun z => (z.1, z.2.1) := by
  rw [btFind_sorted_eq_find? Prod.snd kiItemLess (fun _ _ => Iff.rfl) _
    (by unfold itemsOfEntries at hs ⊢; rw [List.pairwise_map] at hs; rw [List.pairwise_map, List.pairwise_map]; exact hs)]
  unfold itemsOfEntries
  rw [List.find?_map]
  rfl

theorem idxGet_entries (L : List IdxEntry) (hs : (itemsOfEntries L).Pairwise kiItemLess) (k : GoString) :
    idxGet (idxOfEntries L) k = (L.find? fun z => decide (z.2.1 = k)).map fun z => z.2.2 := by
  rw [idxGet_eq_find? _ (idxOfEntries_sorted hs)]
  unfold idxOfEntries
  rw [List.find?_map, Option.map_map]
  rfl

/-- Inserting an entry (by key) commutes with the projections. -/
theorem itemsOfEntries_btInsert (z : IdxEntry) (L : List IdxEntry) :
    itemsOfEntries (btInsert entryLess z L) = btInsert kiItemLess (z.1, z.2.1) (itemsOfEntries L) := by
  unfold itemsOfEntries
  rw [btInsert_map (lessA := entryLess) (lessB := kiItemLess) (fun z => (z.1, z.2.1)) z L
    (fun _ _ => ⟨Iff.rfl, Iff.rfl⟩)]

theorem idxOfEntries_btInsert (z : IdxEntry) (L : List IdxEntry) :
    idxOfEntries (btInsert entryLess z L) = btInsert idxLess (z.2.1, z.2.2) (idxOfEntries L) := by
  unfold idxOfEntries
  rw [btInsert_map (lessA := entryLess) (lessB := idxLess) (fun z => (z.2.1, z.2.2)) z L
    (fun _ _ => ⟨Iff.rfl, Iff.rfl⟩)]

theorem entryLess_swo : StrictWeakOrder entryLess where
  irrefl a := goStringLt_irrefl a.2.1
  trans _ _ _ h1 h2 := goStringLt_trans h1 h2
  incomp_trans a b c h1 h2 h3 h4 := by
    have e1 := goStringLt_eq_of_not_lt h1 h2
    have e2 := goStringLt_eq_of_not_lt h3 h4
    unfold entryLess
    rw [e1, e2]
    exact ⟨goStringLt_irrefl _, goStringLt_irrefl _⟩

theorem itemsOfEntries_sorted_iff (L : List IdxEntry) :
    (itemsOfEntries L).Pairwise kiItemLess ↔ L.Pairwise entryLess := by
  unfold itemsOfEntries; rw [List.pairwise_map]; rfl

/-- Replacing the entry at `i` (its key kept) is `btInsert` of the new one, on sorted entries. -/
theorem btInsert_set_entry : ∀ (L : List IdxEntry), L.Pairwise entryLess → ∀ (i : Nat) (z z' : IdxEntry),
    L[i]? = some z → z'.2.1 = z.2.1 → btInsert entryLess z' L = L.set i z'
  | [], _, i, _, _, h, _ => by simp at h
  | w :: ws, hs, 0, z, z', h, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    unfold btInsert
    have h1 : ¬ entryLess w z' := by unfold entryLess; rw [hk]; exact goStringLt_irrefl _
    have h2 : ¬ entryLess z' w := by unfold entryLess; rw [hk]; exact goStringLt_irrefl _
    rw [ite_eq_right h1, ite_eq_right h2]
    rfl
  | w :: ws, hs, i + 1, z, z', h, hk => by
    simp only [List.getElem?_cons_succ] at h
    rw [List.pairwise_cons] at hs
    have hz : z ∈ ws := List.mem_of_getElem? h
    have hw : entryLess w z := hs.1 z hz
    unfold btInsert
    have h1 : entryLess w z' := by unfold entryLess at *; rw [hk]; exact hw
    rw [ite_eq_left h1, btInsert_set_entry ws hs.2 i z z' h hk]
    rfl

theorem itemsOfEntries_set (L : List IdxEntry) (i : Nat) (z z' : IdxEntry) (h : L[i]? = some z)
    (hp : z'.1 = z.1) (hk : z'.2.1 = z.2.1) : itemsOfEntries (L.set i z') = itemsOfEntries L := by
  unfold itemsOfEntries
  rw [List.map_set]
  apply List.ext_getElem?
  intro j
  by_cases hj : j = i
  · subst hj
    rw [List.getElem?_set_self (by rw [List.length_map]; exact (List.getElem?_eq_some_iff.1 h).1),
      List.getElem?_map, h]
    simp [hp, hk]
  · rw [List.getElem?_set_ne (Ne.symm hj)]

theorem idxOfEntries_set (L : List IdxEntry) (i : Nat) (z' : IdxEntry) :
    idxOfEntries (L.set i z') = (idxOfEntries L).set i (z'.2.1, z'.2.2) := by
  unfold idxOfEntries; rw [List.map_set]

/-- `btInsert` of a key the index has, on sorted entries: the entry at its position replaced. -/
theorem btInsert_idx_set (L : List IdxEntry) (hs : (itemsOfEntries L).Pairwise kiItemLess) (i : Nat)
    (z : IdxEntry) (hz : ∃ h : i < L.length, L[i] = z) (ki : KeyIndex) :
    btInsert idxLess (z.2.1, ki) (idxOfEntries L) = idxOfEntries (L.set i (z.1, z.2.1, ki)) := by
  rw [← idxOfEntries_btInsert (z.1, z.2.1, ki) L,
    btInsert_set_entry L ((itemsOfEntries_sorted_iff L).1 hs) i z (z.1, z.2.1, ki)
      (List.getElem?_eq_some_iff.2 hz) rfl]

/-- The position of a found entry. -/
theorem find?_entry_getElem? (L : List IdxEntry) (k : GoString) (z : IdxEntry)
    (h : L.find? (fun z => decide (z.2.1 = k)) = some z) : ∃ i : Nat, L[i]? = some z ∧ z.2.1 = k := by
  have hz := List.mem_of_find?_eq_some h
  have hk := List.find?_some h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hz
  exact ⟨i, hi, by simpa using hk⟩

theorem find?_entry_none (L : List IdxEntry) (k : GoString)
    (h : L.find? (fun z => decide (z.2.1 = k)) = none) : ∀ z ∈ L, z.2.1 ≠ k := by
  intro z hz
  have := List.find?_eq_none.1 h z hz
  simpa using this

/-! ### Range reads: the keys in `[k, e)` with their answers -/

/-- A key is in `[k, e)` (`e = []`: no upper bound). -/
def inRange (k e key : GoString) : Bool :=
  !decide (go.GoStringLt key k) && (decide (e = []) || decide (go.GoStringLt key e))

/-- The entries of the tree in `[k, e)`, in key order (what `unsafeVisit` visits). -/
def rangeEntries (L : List IdxEntry) (k e : GoString) : List IdxEntry :=
  L.filter fun z => inRange k e z.2.1

/-- The keys of `idx` in `[k, e)` that have an answer at `atRev`, with it, in key order. -/
def rangeAt (idx : IndexM) (k e : GoString) (atRev : w64) : List (GoString × Rev × Rev × w64) :=
  (idx.filter fun z => inRange k e z.1).filterMap fun z => (kiGet z.2 atRev).map fun r => (z.1, r)

/-- `limit`, if positive. -/
def limitOf (limit : w64) : Option Nat :=
  if 0 < sint.Z limit then some (sint.Z limit).toNat else none

def takeLimit {α : Type} (lim : Option Nat) (l : List α) : List α :=
  match lim with
  | some n => l.take n
  | none => l

/-- The count a range read returns: all the answers, or at most the limit when they are not all
counted. -/
def totalOf (lim : Option Nat) (withTotal : Bool) (n : Nat) : Nat :=
  match lim, withTotal with
  | some m, false => min n m
  | _, _ => n

/-- The key index of a key in an index (the empty one if it has none). -/
def kiAt (idx : IndexM) (key : GoString) : KeyIndex := (idxGet idx key).getD kiEmpty

/-- `idxGet` of an entry's key, on sorted entries, is the entry. -/
theorem idxGet_of_mem : ∀ (idx : IndexM), idx.Pairwise idxLess → ∀ z ∈ idx, idxGet idx z.1 = some z.2
  | [], _, _, hz => by simp at hz
  | w :: ws, hs, z, hz => by
    rw [List.pairwise_cons] at hs
    rw [idxGet_eq_find? _ (List.pairwise_cons.2 hs), List.find?_cons]
    rcases List.mem_cons.1 hz with rfl | hz
    · simp
    · have hlt : idxLess w z := hs.1 z hz
      have hne : w.1 ≠ z.1 := fun h => goStringLt_irrefl _ (by unfold idxLess at hlt; rw [h] at hlt; exact hlt)
      simp only [hne, decide_false]
      rw [← idxGet_eq_find? _ hs.2]
      exact idxGet_of_mem ws hs.2 z hz

theorem kiAt_of_mem {idx : IndexM} (hs : idx.Pairwise idxLess) {z : GoString × KeyIndex} (hz : z ∈ idx) :
    kiAt idx z.1 = z.2 := by
  unfold kiAt; rw [idxGet_of_mem idx hs z hz]; rfl

theorem filterMap_congr' {α β : Type} {f g : α → Option β} : ∀ (l : List α), (∀ x ∈ l, f x = g x) →
    l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h x List.mem_cons_self,
      filterMap_congr' l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- The range read, key by key. -/
theorem rangeAt_eq_keys (idx : IndexM) (hs : idx.Pairwise idxLess) (k e : GoString) (atRev : w64) :
    rangeAt idx k e atRev =
      ((idx.map Prod.fst).filter (inRange k e)).filterMap fun key =>
        (kiGet (kiAt idx key) atRev).map fun r => (key, r) := by
  unfold rangeAt
  rw [List.filter_map, List.filterMap_map]
  apply filterMap_congr'
  intro z hz
  rw [List.mem_filter] at hz
  simp only [Function.comp]
  rw [kiAt_of_mem hs hz.1]

theorem kiAt_indexOf (evs : List Ev) (key : GoString) : kiAt (indexOf evs) key = kiOfKey evs key :=
  (indexOf_rep evs).2 key

theorem kiEmpty_head : (kiEmpty.gens.headD Gen.empty).revs = [] := rfl

/-- A key is in the index iff its key index is not the empty one. -/
theorem mem_keys_iff (evs : List Ev) (key : GoString) :
    key ∈ (indexOf evs).map Prod.fst ↔ kiOfKey evs key ≠ kiEmpty := by
  constructor
  · intro h
    rw [List.mem_map] at h
    obtain ⟨z, hz, rfl⟩ := h
    rw [← kiAt_indexOf, kiAt_of_mem (indexOf_sorted evs) hz]
    intro he
    have := indexOf_head' evs z hz
    rw [he] at this
    exact this kiEmpty_head
  · intro h
    rw [← kiAt_indexOf] at h
    unfold kiAt at h
    cases hg : idxGet (indexOf evs) key with
    | none => rw [hg] at h; exact absurd rfl h
    | some ki =>
      unfold idxGet at hg
      cases hf : btFind idxLess (key, KeyIndex.fresh) (indexOf evs) with
      | none => rw [hf] at hg; simp at hg
      | some z =>
        have hmem := btFind_mem hf
        have heq := btFind_equiv hf
        have hk : z.1 = key := goStringLt_eq_of_not_lt heq.1 heq.2
        rw [List.mem_map]
        exact ⟨z, hmem, hk⟩

theorem head_ne_apply {ki : KeyIndex} (h : (ki.gens.headD Gen.empty).revs ≠ []) (e : Ev) :
    ((kiApply ki e).gens.headD Gen.empty).revs ≠ [] := by
  have := KiHead.apply (Or.inr h) e
  rcases this with h' | h'
  · exfalso
    unfold kiApply at h'
    split at h'
    · split at h'
      · rw [h'] at h; exact h kiEmpty_head
      · have hh := kiPut_head (Or.inr h) e.rev
        have := congrArg (fun ki => (ki.gens.headD Gen.empty).revs) h'
        simp only [kiTombstone_gens] at this
        cases hg : (kiPut ki e.rev).gens with
        | nil => exact absurd hg (kiPut_gens_ne_nil _ _)
        | cons g t =>
          rw [hg] at this hh
          simp only [List.cons_append, List.headD_cons] at this hh
          rw [this] at hh
          exact hh kiEmpty_head
    · have hh := kiPut_head (Or.inr h) e.rev
      rw [h'] at hh
      exact hh kiEmpty_head
  · exact h'

theorem head_ne_fold (k : GoString) : ∀ (es : List Ev) (ki : KeyIndex),
    (ki.gens.headD Gen.empty).revs ≠ [] → ((kiFold ki es k).gens.headD Gen.empty).revs ≠ []
  | [], _, h => h
  | e :: es, ki, h => by
    rw [kiFold_cons]
    apply head_ne_fold k es
    split
    · exact head_ne_apply h e
    · exact h

/-- A key the index has stays in it. -/
theorem kiOfKey_ne_mono (evs more : List Ev) (key : GoString) (h : kiOfKey evs key ≠ kiEmpty) :
    kiOfKey (evs ++ more) key ≠ kiEmpty := by
  have hh : ((kiOfKey evs key).gens.headD Gen.empty).revs ≠ [] := by
    rcases KiHead.kiOfKey evs key with h' | h'
    · exact absurd h' h
    · exact h'
  rw [kiOfKey_eq_kiFold, kiFold_append, ← kiOfKey_eq_kiFold]
  intro he
  have := head_ne_fold key more _ hh
  rw [he] at this
  exact this kiEmpty_head

/-- A key has an index in the index of `evs` exactly when its key index is not the empty one
(an index's first generation has a revision: `indexOf_head'`). -/
theorem idxGet_indexOf_eq_none_iff (evs : List Ev) (k : GoString) :
    idxGet (indexOf evs) k = none ↔ kiOfKey evs k = kiEmpty := by
  have hrep := (indexOf_rep evs).2 k
  constructor
  · intro h; rw [h] at hrep; exact hrep.symm
  · intro h
    cases hg : idxGet (indexOf evs) k with
    | none => rfl
    | some ki =>
      exfalso
      rw [hg, Option.getD_some, h] at hrep
      rw [idxGet_eq_find? _ (indexOf_sorted evs)] at hg
      obtain ⟨z, hz, hzk⟩ := Option.map_eq_some_iff.1 hg
      have := indexOf_head' evs z (List.mem_of_find?_eq_some hz)
      rw [hzk, hrep] at this
      exact this kiEmpty_head

/-- A subset of a strictly sorted list, sorted, is a sublist. -/
theorem sublist_of_subset_sorted : ∀ (S T : List GoString), S.Pairwise go.GoStringLt →
    T.Pairwise go.GoStringLt → (∀ x ∈ S, x ∈ T) → S.Sublist T
  | [], T, _, _, _ => List.nil_sublist T
  | s :: S, [], _, _, h => absurd (h s List.mem_cons_self) (by simp)
  | s :: S, t :: T, hS, hT, h => by
    rw [List.pairwise_cons] at hS hT
    by_cases hst : s = t
    · subst hst
      apply List.Sublist.cons_cons
      apply sublist_of_subset_sorted S T hS.2 hT.2
      intro x hx
      have hx' := h x (List.mem_cons_of_mem _ hx)
      rcases List.mem_cons.1 hx' with rfl | hx'
      · exact absurd (hS.1 x hx) (goStringLt_irrefl x)
      · exact hx'
    · apply List.Sublist.cons
      apply sublist_of_subset_sorted (s :: S) T (List.pairwise_cons.2 hS) hT.2
      intro x hx
      have hx' := h x hx
      rcases List.mem_cons.1 hx' with rfl | hx'
      · -- `t ∈ s :: S` with `s ≠ t`: `t ∈ S`, so `s < t`; but `t ∉ T`, and `s ∈ t :: T`
        exfalso
        rcases List.mem_cons.1 hx with hxs | hxS
        · exact hst hxs.symm
        · have hlt := hS.1 x hxS
          have hs' := h s List.mem_cons_self
          rcases List.mem_cons.1 hs' with hs' | hs'
          · exact hst hs'
          · exact goStringLt_irrefl _ (goStringLt_trans hlt (hT.1 s hs'))
      · exact hx'

theorem filterMap_sublist_eq {α β : Type} (f : α → Option β) : ∀ {S T : List α}, S.Sublist T →
    T.Nodup → (∀ x ∈ T, x ∉ S → f x = none) → T.filterMap f = S.filterMap f := by
  intro S T hsub
  induction hsub with
  | slnil => intro _ _; rfl
  | cons a hsub ih =>
    intro hnd h
    rw [List.nodup_cons] at hnd
    rw [List.filterMap_cons]
    have ha : f a = none := h a List.mem_cons_self (fun hm => hnd.1 (hsub.subset hm))
    rw [ha]
    exact ih hnd.2 (fun x hx hnx => h x (List.mem_cons_of_mem _ hx) hnx)
  | cons_cons a hsub ih =>
    intro hnd h
    rw [List.nodup_cons] at hnd
    rw [List.filterMap_cons, List.filterMap_cons, ih hnd.2 (fun x hx hnx =>
      h x (List.mem_cons_of_mem _ hx) (fun hm => by
        rcases List.mem_cons.1 hm with rfl | hm
        · exact hnd.1 hx
        · exact hnx hm))]

theorem keys_sorted (evs : List Ev) : ((indexOf evs).map Prod.fst).Pairwise go.GoStringLt := by
  rw [List.pairwise_map]; exact indexOf_sorted evs

theorem nodup_of_sorted {l : List GoString} (h : l.Pairwise go.GoStringLt) : l.Nodup :=
  List.Pairwise.imp (fun {a b} hlt (he : a = b) => by subst he; exact goStringLt_irrefl _ hlt) h

/-- **A reader's answer** (pure): the index's history (`ilog`, `pend`) and a certified log
`log₀` are comparable lower bounds, and the index had at least `log₀`'s events; below
`log₀.length` the answer is `log₀`'s. -/
theorem reader_answer (log₀ ilog : Log) (pend : List Change)
    (hcmp : histOf log₀ <+: histShape ilog pend ∨ histShape ilog pend <+: histOf log₀)
    (hcount : (evsOf log₀).length ≤ (evsOf (ilog ++ [pend])).length)
    (hlen : ilog.length < 2 ^ 63) (hwf : LogWf' log₀) (hcs : ∀ cs ∈ log₀, cs.length < 2 ^ 63)
    (k : GoString) (r : Nat) (hr : r < log₀.length) :
    kiGet (kiOfKey (evsOf (ilog ++ [pend])) k) (W64 r) = kiGet (kiOfKey (evsOf log₀) k) (W64 r) := by
  rcases hcmp with hpre | hpre
  · exact kiGet_reader log₀ ilog pend hpre hlen hwf hcs k r hr
  · have := evsOfHist_prefix_of_count (histShape ilog pend) log₀ hpre
      (by rw [evsOfHist_histShape]; exact hcount)
    rw [evsOfHist_histShape] at this
    rw [this]

/-- A reader's history is the certified log's events followed by later ones. -/
theorem reader_prefix (log₀ ilog : Log) (pend : List Change)
    (hcmp : histOf log₀ <+: histShape ilog pend ∨ histShape ilog pend <+: histOf log₀)
    (hcount : (evsOf log₀).length ≤ (evsOf (ilog ++ [pend])).length) (hlen : ilog.length < 2 ^ 63) :
    ∃ rest, evsOf (ilog ++ [pend]) = evsOf log₀ ++ rest := by
  rcases hcmp with hpre | hpre
  · obtain ⟨rest, h, -, -⟩ := histOf_prefix_shape log₀ ilog pend hpre hlen
    exact ⟨rest, h⟩
  · have := evsOfHist_prefix_of_count _ _ hpre (by rw [evsOfHist_histShape]; exact hcount)
    rw [evsOfHist_histShape] at this
    exact ⟨[], by rw [this, List.append_nil]⟩

/-- **A reader's range answer** is the certified log's, below its length. -/
theorem reader_range (log₀ ilog : Log) (pend : List Change)
    (hcmp : histOf log₀ <+: histShape ilog pend ∨ histShape ilog pend <+: histOf log₀)
    (hcount : (evsOf log₀).length ≤ (evsOf (ilog ++ [pend])).length)
    (hlen : ilog.length < 2 ^ 63) (hwf : LogWf' log₀) (hcs : ∀ cs ∈ log₀, cs.length < 2 ^ 63)
    (k e : GoString) (r : Nat) (hr : r < log₀.length) :
    rangeAt (indexOf (evsOf (ilog ++ [pend]))) k e (W64 r) =
      rangeAt (indexOf (evsOf log₀)) k e (W64 r) := by
  rw [rangeAt_eq_keys _ (indexOf_sorted _), rangeAt_eq_keys _ (indexOf_sorted _)]
  obtain ⟨rest, hrest⟩ := reader_prefix log₀ ilog pend hcmp hcount hlen
  have hans : ∀ key, kiGet (kiAt (indexOf (evsOf (ilog ++ [pend]))) key) (W64 r) =
      kiGet (kiAt (indexOf (evsOf log₀)) key) (W64 r) := by
    intro key
    rw [kiAt_indexOf, kiAt_indexOf]
    exact reader_answer log₀ ilog pend hcmp hcount hlen hwf hcs key r hr
  simp only [hans]
  have hsub : (((indexOf (evsOf log₀)).map Prod.fst).filter (inRange k e)).Sublist
      (((indexOf (evsOf (ilog ++ [pend]))).map Prod.fst).filter (inRange k e)) := by
    apply List.Sublist.filter
    apply sublist_of_subset_sorted _ _ (keys_sorted _) (keys_sorted _)
    intro x hx
    rw [mem_keys_iff] at hx ⊢
    rw [hrest]
    exact kiOfKey_ne_mono _ _ _ hx
  apply filterMap_sublist_eq _ hsub (nodup_of_sorted ((keys_sorted _).filter _))
  intro x hx hnx
  rw [List.mem_filter] at hx
  have hx0 : x ∉ (indexOf (evsOf log₀)).map Prod.fst := fun h => hnx (List.mem_filter.2 ⟨h, hx.2⟩)
  rw [mem_keys_iff] at hx0
  have he : kiOfKey (evsOf log₀) x = kiEmpty := Classical.byContradiction fun h => hx0 h
  rw [kiAt_indexOf, he, kiGet_kiEmpty]
  rfl

/-! ### What `unsafeVisit` visits: the entries at or above `k`, until one at or above `e` -/

/-- The entries at or above `k` (what `AscendGreaterOrEqual` visits). -/
def fromKey (L : List IdxEntry) (k : GoString) : List IdxEntry :=
  L.filter fun z => !decide (go.GoStringLt z.2.1 k)

/-- Below `e` (or no bound). -/
def belowEnd (e : GoString) (z : IdxEntry) : Bool := decide (e = []) || decide (go.GoStringLt z.2.1 e)

theorem rangeEntries_eq (L : List IdxEntry) (k e : GoString) :
    rangeEntries L k e = (fromKey L k).filter (belowEnd e) := by
  unfold rangeEntries fromKey belowEnd inRange
  rw [List.filter_filter]
  apply List.filter_congr
  intro z _
  exact Bool.and_comm _ _

theorem btAscendGe_entries (L : List IdxEntry) (q : Loc) (k : GoString) :
    btAscendGe kiItemLess (q, k) (itemsOfEntries L) = itemsOfEntries (fromKey L k) := by
  unfold btAscendGe fromKey itemsOfEntries
  rw [List.filter_map]
  rfl

theorem fromKey_sorted {L : List IdxEntry} (hs : L.Pairwise entryLess) (k : GoString) :
    (fromKey L k).Pairwise entryLess := hs.filter _

theorem fromKey_sublist (L : List IdxEntry) (k : GoString) : (fromKey L k).Sublist L :=
  List.filter_sublist

/-- On sorted entries, those below `e` are a prefix: `filter` is `takeWhile`. -/
theorem filter_belowEnd_eq_takeWhile (e : GoString) : ∀ (G : List IdxEntry), G.Pairwise entryLess →
    G.filter (belowEnd e) = G.takeWhile (belowEnd e)
  | [], _ => rfl
  | z :: G, hs => by
    rw [List.pairwise_cons] at hs
    rw [List.filter_cons, List.takeWhile_cons]
    by_cases hz : belowEnd e z = true
    · simp only [hz, ↓reduceIte, List.cons.injEq, true_and]
      exact filter_belowEnd_eq_takeWhile e G hs.2
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
      rw [List.filter_eq_nil_iff.2]
      intro w hw
      intro hb
      apply hz
      unfold belowEnd at hb ⊢
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hb ⊢
      rcases hb with hb | hb
      · exact Or.inl hb
      · exact Or.inr (goStringLt_trans (hs.1 w hw) hb)

/-- `takeWhile` through the visited prefix. -/
theorem takeWhile_eq_take {α : Type} (p : α → Bool) : ∀ (G : List α) (i : Nat), (∀ j (h : j < G.length), j < i → p G[j] = true) →
    i ≤ G.length → (i = G.length ∨ ∃ h : i < G.length, p G[i] = false) → G.takeWhile p = G.take i
  | [], 0, _, _, _ => rfl
  | [], i + 1, _, hi, _ => by simp at hi
  | x :: G, 0, _, _, hstop => by
    rcases hstop with h | ⟨_, h⟩
    · simp at h
    · simp only [List.getElem_cons_zero] at h
      rw [List.takeWhile_cons, h]; rfl
  | x :: G, i + 1, hp, hi, hstop => by
    rw [List.takeWhile_cons]
    have hx : p x = true := hp 0 (by simp) (by omega)
    rw [hx]
    simp only [↓reduceIte, List.take_succ_cons, List.cons.injEq, true_and]
    apply takeWhile_eq_take p G i
    · intro j hj hji
      have := hp (j + 1) (by simp; omega) (by omega)
      simpa using this
    · simp at hi; omega
    · rcases hstop with h | ⟨h, hpi⟩
      · left; simp at h; omega
      · right; exact ⟨by simp at h; omega, by simpa using hpi⟩

theorem takeWhile_getElem? {α : Type} (p : α → Bool) : ∀ (G : List α) (i : Nat),
    (∀ j (h : j < G.length), j ≤ i → p G[j] = true) → (G.takeWhile p)[i]? = G[i]?
  | [], _, _ => rfl
  | x :: G, 0, hp => by
    have hx : p x = true := hp 0 (by simp) (Nat.le_refl _)
    rw [List.takeWhile_cons, hx]
    rfl
  | x :: G, i + 1, hp => by
    have hx : p x = true := hp 0 (by simp) (by omega)
    rw [List.takeWhile_cons, hx]
    simp only [↓reduceIte, List.getElem?_cons_succ]
    exact takeWhile_getElem? p G i (fun j hj hji => hp (j + 1) (by simp; omega) (by omega))

/-! ### `Revisions`, `CountRevisions`, `Range`: the model -/

/-- The answers of a range read of the certified `log` (`end == nil`: the one key). -/
def rangeAnswers (log : Log) (endNil : Bool) (k e : GoString) (atRev : w64) :
    List (GoString × Rev × Rev × w64) :=
  if endNil then
    match kiGet (kiOfKey (evsOf log) k) atRev with
    | some r => [(k, r)]
    | none => []
  else rangeAt (indexOf (evsOf log)) k e atRev

/-- The answers `Revisions`/`Range` return (at most the limit), and the count. -/
def rangeTaken (log : Log) (endNil : Bool) (k e : GoString) (atRev limit : w64) :
    List (GoString × Rev × Rev × w64) :=
  if endNil then rangeAnswers log endNil k e atRev
  else takeLimit (limitOf limit) (rangeAnswers log endNil k e atRev)

def rangeTotal (log : Log) (endNil : Bool) (k e : GoString) (atRev limit : w64) (withTotal : Bool) :
    Nat :=
  if endNil then (rangeAnswers log endNil k e atRev).length
  else totalOf (limitOf limit) withTotal (rangeAnswers log endNil k e atRev).length

/-! ### The visitor's accumulation: the answers of a prefix of the visited entries -/

/-- The answers at `atRev` among entries, with their keys (what the visitors of `Revisions`,
`CountRevisions` and `Range` accumulate). -/
def entryAnswers (G : List IdxEntry) (atRev : w64) : List (GoString × Rev × Rev × w64) :=
  G.filterMap fun z => (kiGet z.2.2 atRev).map fun r => (z.2.1, r)

theorem rangeAt_entries (L : List IdxEntry) (k e : GoString) (atRev : w64) :
    rangeAt (idxOfEntries L) k e atRev = entryAnswers (rangeEntries L k e) atRev := by
  unfold rangeAt rangeEntries entryAnswers idxOfEntries
  rw [List.filter_map, List.filterMap_map]
  rfl

theorem entryAnswers_nil (atRev : w64) : entryAnswers [] atRev = [] := rfl

theorem entryAnswers_take_succ (G : List IdxEntry) (atRev : w64) (i : Nat) (z : IdxEntry)
    (hz : G[i]? = some z) :
    entryAnswers (G.take (i + 1)) atRev =
      entryAnswers (G.take i) atRev ++ ((kiGet z.2.2 atRev).map fun r => (z.2.1, r)).toList := by
  unfold entryAnswers
  rw [List.take_add_one, hz, List.filterMap_append]
  cases hg : kiGet z.2.2 atRev <;> simp [hg]

theorem entryAnswers_prefix (G : List IdxEntry) (atRev : w64) (i : Nat) :
    entryAnswers (G.take i) atRev <+: entryAnswers G atRev := by
  unfold entryAnswers
  obtain ⟨t, ht⟩ := List.take_prefix i G
  exact ⟨t.filterMap _, by rw [← List.filterMap_append, ht]⟩

theorem take_append_of_le {α : Type} : ∀ (A t : List α) (m : Nat), m ≤ A.length →
    (A ++ t).take m = A.take m
  | _, _, 0, _ => by simp
  | [], _, _ + 1, hm => by simp at hm
  | a :: A, t, m + 1, hm => by
    simp only [List.cons_append, List.take_succ_cons, List.cons.injEq, true_and]
    exact take_append_of_le A t m (by simp at hm; omega)

theorem take_of_prefix {α : Type} {A B : List α} (h : A <+: B) (m : Nat) (hm : m ≤ A.length) :
    B.take m = A.take m := by
  obtain ⟨t, rfl⟩ := h
  exact take_append_of_le A t m hm

/-- `limit > 0 && len(taken) >= limit`. -/
def reached (lim : Option Nat) (n : Nat) : Bool :=
  match lim with
  | some m => decide (m ≤ n)
  | none => false

theorem reached_takeLimit {α : Type} (lim : Option Nat) (A : List α) :
    reached lim (takeLimit lim A).length = reached lim A.length := by
  cases lim with
  | none => rfl
  | some m =>
    unfold reached takeLimit
    simp only [List.length_take]
    by_cases h : m ≤ A.length
    · simp [h, Nat.min_eq_left h]
    · simp [h, Nat.min_eq_right (Nat.le_of_not_le h)]

theorem takeLimit_append_reached {α : Type} (lim : Option Nat) (A B : List α)
    (h : reached lim A.length = true) : takeLimit lim (A ++ B) = takeLimit lim A := by
  cases lim with
  | none => simp [reached] at h
  | some m =>
    simp only [reached, decide_eq_true_eq] at h
    exact take_append_of_le A B m h

theorem takeLimit_append_not {α : Type} (lim : Option Nat) (A : List α) (a : α)
    (h : reached lim A.length = false) : takeLimit lim (A ++ [a]) = takeLimit lim A ++ [a] := by
  cases lim with
  | none => rfl
  | some m =>
    simp only [reached, decide_eq_false_iff_not, Nat.not_le] at h
    show List.take m (A ++ [a]) = List.take m A ++ [a]
    rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (Nat.le_of_lt h)]

theorem takeLimit_of_prefix {α : Type} (lim : Option Nat) {A B : List α} (hp : A <+: B)
    (h : reached lim A.length = true) : takeLimit lim B = takeLimit lim A := by
  cases lim with
  | none => simp [reached] at h
  | some m =>
    simp only [reached, decide_eq_true_eq] at h
    exact take_of_prefix hp m h

theorem takeLimit_length {α : Type} (lim : Option Nat) (A : List α) :
    (takeLimit lim A).length = totalOf lim false A.length := by
  cases lim with
  | none => rfl
  | some m => simp [takeLimit, totalOf, Nat.min_comm]

theorem totalOf_succ (lim : Option Nat) (withTotal : Bool) (n : Nat)
    (h : withTotal = true ∨ reached lim n = false) :
    totalOf lim withTotal (n + 1) = totalOf lim withTotal n + 1 := by
  cases lim with
  | none => cases withTotal <;> rfl
  | some m =>
    cases withTotal
    · simp only [reached, decide_eq_false_iff_not, Nat.not_le, Bool.false_eq_true, false_or] at h
      simp [totalOf]; omega
    · rfl

theorem totalOf_reached (lim : Option Nat) (n N : Nat) (hn : n ≤ N) (h : reached lim n = true) :
    totalOf lim false N = totalOf lim false n := by
  cases lim with
  | none => simp [reached] at h
  | some m =>
    simp only [reached, decide_eq_true_eq] at h
    simp [totalOf]; omega

theorem totalOf_true (lim : Option Nat) (n : Nat) : totalOf lim true n = n := by
  cases lim <;> rfl

/-- `limit > 0 && len(revs) >= limit`, on the words. -/
theorem reached_words (limit : w64) (s : GoSlice) (n : Nat) (hs : n = sint.nat s.len)
    (hs0 : 0 ≤ sint.Z s.len) :
    (decide (0 < sint.Z limit) && decide (sint.Z limit ≤ sint.Z s.len)) = reached (limitOf limit) n := by
  unfold limitOf reached
  by_cases h : 0 < sint.Z limit
  · simp only [h, ↓reduceIte, decide_true, Bool.true_and]
    subst hs
    unfold sint.nat sint.Z at *
    simp only [decide_eq_decide]
    omega
  · simp [h]

theorem takeLimit_nil {α : Type} (lim : Option Nat) : takeLimit lim ([] : List α) = [] := by
  cases lim <;> simp [takeLimit]

theorem totalOf_zero (lim : Option Nat) (withTotal : Bool) : totalOf lim withTotal 0 = 0 := by
  cases lim <;> cases withTotal <;> rfl

/-- The range answers of the certified log are those of the tree's entries in range (through
the reader's stability, `reader_range`). -/
theorem rangeAnswers_entries (log₀ ilog : Log) (pend : List Change) (L : List IdxEntry)
    (hcmp : histOf log₀ <+: histShape ilog pend ∨ histShape ilog pend <+: histOf log₀)
    (hcount : (evsOf log₀).length ≤ (evsOf (ilog ++ [pend])).length)
    (hlen : ilog.length < 2 ^ 63) (hwf : LogWf' log₀) (hcs : ∀ cs ∈ log₀, cs.length < 2 ^ 63)
    (HLL : idxOfEntries L = indexOf (evsOf (ilog ++ [pend])))
    (k e : GoString) (r : Nat) (hr : r < log₀.length) :
    rangeAnswers log₀ false k e (W64 r) = entryAnswers (rangeEntries L k e) (W64 r) := by
  unfold rangeAnswers
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← reader_range log₀ ilog pend hcmp hcount hlen hwf hcs k e r hr, ← HLL, rangeAt_entries]

theorem rangeAnswers_nil (log : Log) (k e : GoString) (atRev : w64) :
    rangeAnswers log true k e atRev = ((kiGet (kiOfKey (evsOf log) k) atRev).map fun r => (k, r)).toList := by
  unfold rangeAnswers
  cases kiGet (kiOfKey (evsOf log) k) atRev <;> rfl

theorem rangeTaken_true (log : Log) (k e : GoString) (atRev limit : w64) :
    rangeTaken log true k e atRev limit = rangeAnswers log true k e atRev := rfl

theorem rangeTaken_false (log : Log) (k e : GoString) (atRev limit : w64) :
    rangeTaken log false k e atRev limit = takeLimit (limitOf limit) (rangeAnswers log false k e atRev) := rfl

theorem rangeTotal_true (log : Log) (k e : GoString) (atRev limit : w64) (wt : Bool) :
    rangeTotal log true k e atRev limit wt = (rangeAnswers log true k e atRev).length := rfl

theorem rangeTotal_false (log : Log) (k e : GoString) (atRev limit : w64) (wt : Bool) :
    rangeTotal log false k e atRev limit wt =
      totalOf (limitOf limit) wt (rangeAnswers log false k e atRev).length := rfl

end mvcc
end EtcdGrove
end Perennial
