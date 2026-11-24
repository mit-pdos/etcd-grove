-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/InputEndIp.lean` (etc/copy-part.py; rerun it, do not edit).
/-
(#33 S4, decision 3) **The in-progress boundary across an input**, pure: the `RawNode` input forms'
`ip' = min ip (lcpLen ps.log ps'.log)` (`RawNodeAbsSpecs.lean`), from what `Step` does to the log's
`offsetInProgress` (`ip + 1`, `ownRawNodeAt`'s `"%Hip"`). An input that keeps the log's state
(a tick: `logst_of_stepEnd_hup`, `logst_of_stepEnd_beat`, `InputEndLift.lean`) or only appends keeps the
boundary, which is at most the log's length (`ownRaftPhysC_ipFacts`); a `MsgApp` moves it to
`maybeAppendIp` (`HandleAppResult`).
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.InputEndLift
public import KvNet.Proof.go_etcd_io.raft.v3.RawNodeAt
public import KvNet.Proof.go_etcd_io.raft.v3.MaybeAppendIp

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section ip
variable [GooseExts]

theorem lcpLen_nil_left (l : List EntryM) : lcpLen [] l = 0 := by
  cases l <;> rfl

/-- A log and an extension of it agree on the whole log. -/
theorem lcpLen_append_self : ∀ (l x : List EntryM), lcpLen l (l ++ x) = l.length
  | [], x => lcpLen_nil_left x
  | a :: l, x => by
    simp only [List.cons_append, lcpLen, lcpLen_append_self l x, List.length_cons, if_true]

theorem lcpLen_self (l : List EntryM) : lcpLen l l = l.length := by
  simpa using lcpLen_append_self l []

/-- A log cut at `j` and continued by an entry other than its own at `j` agrees with it on `j`
entries exactly (`truncateAndAppend` at a conflict). -/
theorem lcpLen_take_append : ∀ (l x : List EntryM) (j : Nat), j < l.length →
    x.head? ≠ l[j]? → lcpLen l (l.take j ++ x) = j
  | [], _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | a :: l, x, 0, _, hne => by
    cases x with
    | nil => rfl
    | cons b x =>
      have hab : a ≠ b := fun h => hne (by simp [h])
      simp only [List.take_zero, List.nil_append, lcpLen, if_neg hab]
  | a :: l, x, j + 1, hj, hne => by
    simp only [List.take_succ_cons, List.cons_append, lcpLen, if_true]
    rw [lcpLen_take_append l x j (by simpa using hj) (by simpa using hne)]

/-- **The boundary kept by an input that only extends the log**: at most the log's length, it is
the minimum with the common prefix (the whole old log). -/
theorem ip_eq_min_of_append {ip : Nat} {l x : List EntryM} (h : ip ≤ l.length) :
    ip = min ip (lcpLen l (l ++ x)) := by
  rw [lcpLen_append_self]; omega

/-- The same for an input that keeps the log. -/
theorem ip_eq_min_of_eq {ip : Nat} {l l' : List EntryM} (h : ip ≤ l.length) (he : l' = l) :
    ip = min ip (lcpLen l l') := by
  subst he; simpa using ip_eq_min_of_append (x := []) h

/-- `ownRawNodeAt`'s boundary `ip` (`uint.nat inprogress = ip + 1`) is at most the log's length in
the scope (`prev = base0`), from `ownRaftPhysC_ipFacts`' upper bound. -/
theorem ip_le_log {ip : Nat} {ls : LogState} (hip : uint.nat ls.inprogress = ip + 1)
    (hp : uint.Z ls.prev.index' = 0)
    (hb : uint.Z ls.inprogress ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
      + (ls.uents.length : Int) + 1) :
    ip ≤ (ls.sents ++ ls.uents).length := by
  rw [List.length_append]
  have := uint_nat_eq ls.inprogress
  omega

/-- `plogFindConflict` is `0` when every entry matches, else the index of the first entry that does
not (`raftLog__maybeAppend.lean`'s `find_conflict_cases`, restated: a proof file's lemmas are
private). -/
theorem ip_find_conflict_cases (b : entryID) (es ents : List EntryM) :
    (plogFindConflict b es ents = W64 0 ∧ ∀ e ∈ ents, PlogMatches b es (entId e)) ∨
    (∃ (k : Nat) (e : EntryM), ents[k]? = some e ∧
      plogFindConflict b es ents = e.Index' ∧
      ¬ PlogMatches b es (entId e) ∧
      ∀ (j : Nat) e', j < k → ents[j]? = some e' → PlogMatches b es (entId e')) := by
  induction ents with
  | nil => exact .inl ⟨rfl, by simp⟩
  | cons e ents IH =>
    by_cases Hm : PlogMatches b es (entId e)
    · rcases IH with ⟨H0, Hall⟩ | ⟨k, e', Hk, Hci, Hnm, Hbefore⟩
      · refine .inl ⟨?_, ?_⟩
        · simp only [plogFindConflict, ite_eq_left Hm]; exact H0
        · intro x Hx
          rcases List.mem_cons.1 Hx with rfl | Hx
          · exact Hm
          · exact Hall x Hx
      · refine .inr ⟨k + 1, e', by simpa using Hk, ?_, Hnm, ?_⟩
        · simp only [plogFindConflict, ite_eq_left Hm]; exact Hci
        · intro j e'' Hj Hj'
          cases j with
          | zero => simp at Hj'; subst Hj'; try exact Hm
          | succ j => exact Hbefore j e'' (by omega) (by simpa using Hj')
    · refine .inr ⟨0, e, rfl, ?_, Hm, fun j _ Hj _ => absurd Hj (Nat.not_lt_zero _)⟩
      simp only [plogFindConflict, ite_eq_right Hm]

/-- **A `MsgApp`'s boundary** (`maybeAppendIp`, `HandleAppResult`'s accepting arm): at a log from
`base0` whose boundary `ip + 1` is inside it, the new boundary is `min ip` the common prefix of the
log before and after (`plogMaybeAppend`'s): kept when nothing conflicts or the batch continues the
log, else at the conflict `ci`, where the logs first differ (the entry there has another term). -/
theorem maybeAppendIp_lcp {ls : LogState} {prev : entryID} {ents : List EntryM} {lni : w64}
    {es' : List EntryM}
    (hma : plogMaybeAppend ls.prev (ls.sents ++ ls.uents) prev ents = some (lni, es'))
    (hp : uint.Z ls.prev.index' = 0) (hwf : PlogWf prev ents)
    (hlo : 1 ≤ uint.Z ls.inprogress)
    (hhi : uint.Z ls.inprogress ≤ ((ls.sents ++ ls.uents).length : Int) + 1) :
    uint.nat (maybeAppendIp ls ents) - 1 =
      min (uint.nat ls.inprogress - 1) (lcpLen (ls.sents ++ ls.uents) es') := by
  generalize hes : ls.sents ++ ls.uents = es at hma hhi
  have e0 := uint_nat_eq ls.inprogress
  unfold plogMaybeAppend at hma
  split at hma
  case isFalse => cases hma
  case isTrue hpm =>
  simp only [Option.some.injEq, Prod.mk.injEq] at hma
  obtain ⟨-, rfl⟩ := hma
  unfold maybeAppendIp
  rw [hes]
  rcases ip_find_conflict_cases ls.prev es ents with ⟨H0, -⟩ | ⟨k, e, Hk, Hci, Hnm, Hbefore⟩
  · rw [if_pos H0, if_pos H0, lcpLen_self]
    omega
  · have Hke := hwf k e Hk
    have Hne : e.Index' ≠ W64 0 := by
      have h1 : uint.Z e.Index' ≠ 0 := by have := uint_Z_nonneg prev.index'; push_cast at Hke; omega
      intro h; exact h1 (by rw [h]; rfl)
    have Hci1 : 1 ≤ uint.Z e.Index' := by
      have := uint_Z_nonneg prev.index'; push_cast at Hke; omega
    rw [Hci, if_neg Hne, if_neg Hne]
    -- the conflict at most one past the log's end (the entry before it, or `prev`, matched)
    have Hle : uint.Z e.Index' ≤ (es.length : Int) + 1 := by
      cases k with
      | zero =>
        have := (plogTermAt_some_range ls.prev es prev.index' prev.term' hpm).2
        unfold plogLastIndexZ at this
        push_cast at Hke; omega
      | succ k' =>
        obtain ⟨e', He'⟩ : ∃ e', ents[k']? = some e' :=
          ⟨_, List.getElem?_eq_getElem (by have := (List.getElem?_eq_some_iff.1 Hk).1; omega)⟩
        have Hm' := (plogTermAt_some_range ls.prev es _ _ (Hbefore k' e' (by omega) He')).2
        unfold plogLastIndexZ entId at Hm'
        have := hwf k' e' He'
        push_cast at Hke this Hm'; omega
    have Hkd : (uint.Z e.Index' - uint.Z prev.index' - 1).toNat = k := by
      push_cast at Hke; omega
    have Hdk : ents.drop k = e :: ents.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.1 Hk).1,
        (List.getElem?_eq_some_iff.1 Hk).2]
    rw [Hkd, Hdk]
    simp only [plogTruncateAppend, hp, Int.sub_zero]
    have e1 := uint_nat_eq e.Index'
    unfold logTruncInprogress
    have hlen : (ls.sents.length : Int) + (ls.uents.length : Int) = (es.length : Int) := by
      rw [← hes, List.length_append]; push_cast; rfl
    rcases Int.lt_or_eq_of_le Hle with Hlt | Heq
    · -- a truncation: the logs differ at the conflict
      have Hj : (uint.Z e.Index' - 1).toNat < es.length := by omega
      have Hdiff : (e :: ents.drop (k + 1)).head? ≠ es[(uint.Z e.Index' - 1).toNat]? := by
        intro h
        apply Hnm
        unfold PlogMatches plogTermAt entId
        simp only [hp]
        rw [if_neg (by omega), if_neg (by omega), Int.sub_zero, ← h]
        rfl
      rw [lcpLen_take_append es _ _ Hj Hdiff, if_pos (by rw [hp]; push_cast; omega)]
      split <;> omega
    · -- the batch continues the log: kept
      have Ht : es.take (uint.Z e.Index' - 1).toNat = es := List.take_of_length_le (by omega)
      rw [Ht, lcpLen_append_self, if_neg (by rw [hp]; push_cast; omega)]
      omega

end ip

end EtcdGrove
end Perennial
