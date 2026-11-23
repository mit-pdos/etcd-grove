/-
A handler step of replica `i` (idle: no pending broadcast): its state becomes `σ'`, its history
gains the events `E` (the ghost events and the sends, in order), its messages to `to` gain the
direct sends `snd to` and the new pending broadcast's message, and nothing else of `Inv` changes
(`HS`). Generic consequences: events, `evBefore`, messages, deliveries.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.AuxFrame

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace HStepProof

/-- The events outputs log. -/
def evsOf (os : List Out) : List Event := os.filterMap Out.hev

/-- The messages outputs send directly to `to`. -/
def sendsOf (os : List Out) (to : Nat) : List Msg := os.filterMap (Out.sendTo to)

/-- A pending broadcast's message to `to`. -/
def intendedOf (p : Option Bcast) (to : Nat) : List Msg :=
  match p with
  | some b => if to ∈ b.peers then [b.m] else []
  | none => []

/-- A handler step of replica `i`. -/
structure HS (S S' : Sys) (i : Nat) (σ' : RState) (E : List Event) (snd : Nat → List Msg)
    (pend : Option Bcast) : Prop where
  rep : S'.rep = upd S.rep i σ'
  hist : S'.hist = S.hist ++ E.map (fun e => (i, e))
  msgs : ∀ fr to, S'.msgs fr to =
    S.msgs fr to ++ (if fr = i then snd to ++ intendedOf pend to else [])
  sent : S'.sent = S.sent
  pending : S'.pending = upd S.pending i pend
  del : ∀ d, d ∈ S.delivered → d ∈ S'.delivered
  delOk : ∀ fr to n, (fr, to, n) ∈ S'.delivered → (fr, to, n) ∈ S.delivered ∨
    n < (S.sent fr to).length
  ops : S'.ops = S.ops
  owner : S'.owner = S.owner
  execLog : S'.execLog = S.execLog
  execCur : S'.execCur = S.execCur
  execIdx : S'.execIdx = S.execIdx
  gexec : S'.gexec = S.gexec
  fired : S'.fired = S.fired

section
variable {S S' : Sys} {i : Nat} {σ' : RState} {E : List Event} {snd : Nat → List Msg}
  {pend : Option Bcast}

theorem HS.ev_iff (h : HS S S' i σ' E snd pend) (r : Nat) (e : Event) :
    S'.ev r e ↔ S.ev r e ∨ (r = i ∧ e ∈ E) := by
  simp only [Sys.ev, h.hist, List.mem_append, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro (h1 | ⟨e', he', rfl, rfl⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨rfl, he'⟩
  · rintro (h1 | ⟨rfl, he⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨e, he, rfl, rfl⟩

theorem HS.ev_old (h : HS S S' i σ' E snd pend) {r : Nat} {e : Event} (he : S.ev r e) :
    S'.ev r e := (h.ev_iff r e).mpr (Or.inl he)

theorem HS.ev_new (h : HS S S' i σ' E snd pend) {e : Event} (he : e ∈ E) : S'.ev i e :=
  (h.ev_iff i e).mpr (Or.inr ⟨rfl, he⟩)

/-- An event not in `E` (or of another replica) is old. -/
theorem HS.ev_back (h : HS S S' i σ' E snd pend) {r : Nat} {e : Event} (he : S'.ev r e)
    (hn : r = i → e ∉ E) : S.ev r e := by
  rcases (h.ev_iff r e).mp he with h1 | ⟨h1, h2⟩
  · exact h1
  · exact absurd h2 (hn h1)

/-- `e` comes before `e'` in `E`. -/
def EBefore (E : List Event) (e e' : Event) : Prop :=
  ∃ p p' : Nat, p < p' ∧ E[p]? = some e ∧ E[p']? = some e'

theorem HS.evBefore_iff (h : HS S S' i σ' E snd pend) (r : Nat) (e : Event) (r' : Nat)
    (e' : Event) :
    S'.evBefore r e r' e' ↔ S.evBefore r e r' e' ∨ (S.ev r e ∧ r' = i ∧ e' ∈ E) ∨
      (r = i ∧ r' = i ∧ EBefore E e e') := by
  have hlen : ∀ q, q < S.hist.length → S'.hist[q]? = S.hist[q]? := by
    intro q hq; rw [h.hist, List.getElem?_append_left hq]
  have hlen' : ∀ q, S.hist.length ≤ q →
      S'.hist[q]? = (E[q - S.hist.length]?).map (fun e => (i, e)) := by
    intro q hq; rw [h.hist, List.getElem?_append_right hq, List.getElem?_map]
  constructor
  · rintro ⟨p, p', hp, h1, h2⟩
    by_cases hp' : p' < S.hist.length
    · left; exact ⟨p, p', hp, by rw [← hlen p (by omega)]; exact h1, by rw [← hlen p' hp']; exact h2⟩
    · rw [hlen' p' (by omega)] at h2
      cases he' : E[p' - S.hist.length]? with
      | none => rw [he'] at h2; cases h2
      | some e2 =>
        rw [he'] at h2; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        by_cases hpl : p < S.hist.length
        · rw [hlen p hpl] at h1
          exact Or.inr (Or.inl ⟨List.mem_of_getElem? h1, rfl, List.mem_of_getElem? he'⟩)
        · rw [hlen' p (by omega)] at h1
          cases he : E[p - S.hist.length]? with
          | none => rw [he] at h1; cases h1
          | some e1 =>
            rw [he] at h1; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1
            exact Or.inr (Or.inr ⟨rfl, rfl, p - S.hist.length, p' - S.hist.length, by omega, he, he'⟩)
  · rintro (⟨p, p', hp, h1, h2⟩ | ⟨h1, rfl, h2⟩ | ⟨rfl, rfl, p, p', hp, h1, h2⟩)
    · have := (List.getElem?_eq_some_iff.mp h2).1
      exact ⟨p, p', hp, by rw [hlen p (by omega)]; exact h1, by rw [hlen p' this]; exact h2⟩
    · obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp h1
      obtain ⟨p', hp'⟩ := List.mem_iff_getElem?.mp h2
      have hl := (List.getElem?_eq_some_iff.mp hp).1
      refine ⟨p, S.hist.length + p', by omega, by rw [hlen p hl]; exact hp, ?_⟩
      rw [hlen' _ (by omega)]; simp [hp']
    · refine ⟨S.hist.length + p, S.hist.length + p', by omega, ?_, ?_⟩
      · rw [hlen' _ (by omega)]; simp [h1]
      · rw [hlen' _ (by omega)]; simp [h2]

theorem HS.evBefore_old (h : HS S S' i σ' E snd pend) {r r' : Nat} {e e' : Event}
    (hb : S.evBefore r e r' e') : S'.evBefore r e r' e' :=
  (h.evBefore_iff r e r' e').mpr (Or.inl hb)

/-- `evBefore` into an old event is old. -/
theorem HS.evBefore_back (h : HS S S' i σ' E snd pend) {r r' : Nat} {e e' : Event}
    (hb : S'.evBefore r e r' e') (he' : S.ev r' e') (hn : r' = i → e' ∉ E) :
    S.evBefore r e r' e' := by
  rcases (h.evBefore_iff r e r' e').mp hb with h1 | ⟨-, h2, h3⟩ | ⟨-, h2, p, p', -, -, h3⟩
  · exact h1
  · exact absurd h3 (hn h2)
  · exact absurd (List.mem_of_getElem? h3) (hn h2)

theorem HS.count_eq (h : HS S S' i σ' E snd pend) {r : Nat} {e : Event} (he : r = i → e ∉ E) :
    (S'.hist.filter (· = (r, e))).length = (S.hist.filter (· = (r, e))).length := by
  rw [h.hist, List.filter_append, List.length_append]
  have : (E.map (fun e => (i, e))).filter (· = (r, e)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro y hy hye
    simp only [decide_eq_true_eq] at hye
    subst hye
    simp only [List.mem_map, Prod.mk.injEq] at hy
    obtain ⟨e', he', rfl, rfl⟩ := hy
    exact he rfl he'
  rw [this]; rfl

theorem HS.mem_msgs (h : HS S S' i σ' E snd pend) {fr to : Nat} {m : Msg} :
    m ∈ S'.msgs fr to ↔ m ∈ S.msgs fr to ∨ (fr = i ∧ (m ∈ snd to ∨ m ∈ intendedOf pend to)) := by
  rw [h.msgs]
  by_cases hf : fr = i
  · simp [hf]
  · simp [hf]

theorem HS.msgs_old (h : HS S S' i σ' E snd pend) {fr to : Nat} {m : Msg}
    (hm : m ∈ S.msgs fr to) : m ∈ S'.msgs fr to := h.mem_msgs.mpr (Or.inl hm)

theorem HS.deliveredMsg_old (h : HS S S' i σ' E snd pend) {a r : Nat} {m : Msg}
    (hd : S.deliveredMsg a r m) : S'.deliveredMsg a r m := by
  obtain ⟨n, h1, h2⟩ := hd
  exact ⟨n, by rw [h.sent]; exact h1, h.del _ h2⟩

theorem HS.rep_other (h : HS S S' i σ' E snd pend) {r : Nat} (hr : r ≠ i) :
    S'.rep r = S.rep r := by rw [h.rep, upd_other _ _ _ _ hr]

theorem HS.rep_self (h : HS S S' i σ' E snd pend) : S'.rep i = σ' := by rw [h.rep, upd_same]

/-- The messages' positions: old positions keep their message. -/
theorem HS.getElem_old (h : HS S S' i σ' E snd pend) {fr to n : Nat} {m : Msg}
    (hm : (S.msgs fr to)[n]? = some m) : (S'.msgs fr to)[n]? = some m := by
  rw [h.msgs, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hm).1, hm]

/-- A count grows by the new messages' count. -/
theorem HS.cnt_eq (h : HS S S' i σ' E snd pend) (fr to : Nat) (p : Msg → Bool) :
    S'.cnt fr to p = S.cnt fr to p +
      (if fr = i then ((snd to ++ intendedOf pend to).filter p).length else 0) := by
  simp only [Sys.cnt, h.msgs, List.filter_append, List.length_append]
  split <;> simp

/-- `allDeliv` is kept when no new message satisfies `p` (and deliveries only grow). -/
theorem HS.allDeliv_old (h : HS S S' i σ' E snd pend) {fr to : Nat} {p : Msg → Bool}
    (ha : S.allDeliv fr to p)
    (hnew : fr = i → ∀ m, m ∈ snd to ++ intendedOf pend to → p m = false) :
    S'.allDeliv fr to p := by
  intro n m hn hp
  rw [h.msgs] at hn
  by_cases hl : n < (S.msgs fr to).length
  · rw [List.getElem?_append_left hl] at hn; exact h.del _ (ha n m hn hp)
  · rw [List.getElem?_append_right (by omega)] at hn
    split at hn
    · rename_i hf
      have := hnew hf m (List.mem_of_getElem? hn); rw [this] at hp; cases hp
    · simp at hn

end

/-! ## `applyStep` from an idle replica -/

theorem hist_applyStep (S : Sys) (i : Nat) (σ : RState) (os : List Out) :
    (S.applyStep i (σ, os)).hist = S.hist ++ (evsOf os).map (fun e => (i, e)) := by
  rw [Sys.applyStep_hist]
  congr 1
  simp only [evsOf]
  induction os with
  | nil => rfl
  | cons o os ih =>
    cases h : Out.hev o <;> simp [List.filterMap_cons, h, ih]

theorem msgs_applyStep (S : Sys) (i : Nat) (σ : RState) (os : List Out) (hp : S.pending i = none)
    (fr to : Nat) :
    (S.applyStep i (σ, os)).msgs fr to =
      S.msgs fr to ++ (if fr = i then sendsOf os to ++ intendedOf (pendFold os none) to else []) := by
  simp only [Sys.msgs, Sys.intended, Sys.applyStep_sent, Sys.applyStep_outbox,
    Sys.applyStep_pending, sendsOf, intendedOf]
  by_cases hf : fr = i
  · subst hf; simp [hp, List.append_assoc]; rfl
  · simp [hf]

theorem deliver_delivered (S : Sys) (fr i n : Nat) (m : Msg) :
    (fr, i, n) ∈ (S.deliver fr i n m).delivered := by
  have hd : S.deliver fr i n m =
      ({ S with delivered := S.delivered ++ [(fr, i, n)] } : Sys).applyStep i
        ((hMsg (S.rep i) m).1, (hMsg (S.rep i) m).2) := rfl
  rw [hd, Sys.applyStep_delivered]; simp

/-- A delivery step is a handler step. -/
theorem hs_deliver (S : Sys) (fr i n : Nat) (m : Msg) (hidle : S.idle i)
    (hm : (S.sent fr i)[n]? = some m) :
    HS S (S.deliver fr i n m) i (hMsg (S.rep i) m).1 (evsOf (hMsg (S.rep i) m).2)
      (sendsOf (hMsg (S.rep i) m).2) (pendFold (hMsg (S.rep i) m).2 none) := by
  have hd : S.deliver fr i n m =
      ({ S with delivered := S.delivered ++ [(fr, i, n)] } : Sys).applyStep i
        ((hMsg (S.rep i) m).1, (hMsg (S.rep i) m).2) := rfl
  rw [hd]
  have hp : ({ S with delivered := S.delivered ++ [(fr, i, n)] } : Sys).pending i = none :=
    hidle.1
  refine ⟨by simp, by rw [hist_applyStep], fun fr' to => ?_, by simp, ?_, ?_, ?_, by simp,
    by simp, by simp, by simp, by simp, by simp, by simp⟩
  · rw [msgs_applyStep _ _ _ _ hp]; rfl
  · funext r; simp only [Sys.applyStep_pending, upd_apply]; split <;> simp_all
  · intro d hd'; simp only [Sys.applyStep_delivered]; exact List.mem_append_left _ hd'
  · intro fr' to n' hd'
    simp only [Sys.applyStep_delivered, List.mem_append, List.mem_singleton,
      Prod.mk.injEq] at hd'
    rcases hd' with h1 | ⟨rfl, rfl, rfl⟩
    · exact Or.inl h1
    · exact Or.inr (List.getElem?_eq_some_iff.mp hm).1

end HStepProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
