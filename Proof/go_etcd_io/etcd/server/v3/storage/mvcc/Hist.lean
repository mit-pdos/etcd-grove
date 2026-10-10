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
  { rev := ⟨W64 m, W64 i⟩, key := c.key, tomb := c.isDel }

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
    · rw [if_pos hk]
      have hrevs' : ∀ x ∈ kiRevs (kiApply ki e), x.main.toNat ≤ e.rev.main.toNat := by
        intro x hx
        rcases kiApply_revs hwf e x hx with hx | hx
        · exact Nat.le_trans (hrevs x hx) hge
        · rw [hx]; exact Nat.le_refl _
      rw [kiGet_fold_below k es (kiApply ki e) e.rev.main.toNat (kiApply_wf hwf e) hrevs' hlt hes' r
        (by omega)]
      exact kiGet_kiApply_below hwf hb hrevs e hge hlt hr
    · rw [if_neg hk]
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

end mvcc
end EtcdGrove
end Perennial
