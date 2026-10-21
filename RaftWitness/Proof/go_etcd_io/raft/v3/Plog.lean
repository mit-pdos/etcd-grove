/-
Port of `election_proof/plog.v` at feb5c73d4: pure functions on a raft log, shared by
the protocol model and the `raftLog` specs.

A log is a compaction boundary `b : entryID` -- the last entry whose payload has been
discarded but whose term is still known -- and the entries after it,
`es : List EntryM`, at indices `b.index + 1, b.index + 2, ...` (`PlogWf`). This
is exactly how `ownRaftLog` (`InvRaftlog.lean`) describes the physical log (`prev`,
`sents ++ uents`), and it is what the protocol state (`PState`, `Protocol/Model.lean`)
carries, so one set of functions serves both: a `raftLog` method's spec says it
computes `plogF prev (sents ++ uents) args`, and the model's rule says the node moves
to `plogF base log args`. Each function mirrors one Go function of `log.go` /
`log_unstable.go`, named in its comment; read the Go before changing one.

Entries are the wire type `EntryM`: `Term'`, `Index'`, `Type'`, `Data'`. Only
the first two are ever read here. See notes/raft-replication-model.md.

Lean notes: Rocq's `l !! k` on lists is `l[k]?`, `list.last` is `List.getLast?`,
`Z.to_nat` is `Int.toNat`, `S k` (as a `Z`) is `((k + 1 : Nat) : Int)` (as in
`LogIndicesOk`), `decide`/`bool_decide` are `if`/`decide`; the `Decision` instance of
`plog_matches` is a `Decidable` instance. Prop-valued definitions are UpperCamel
(`PlogWf`, `PlogMatches`), so lemma names keep them as written (`PlogWf_app`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Proof.go_etcd_io.raft.v3.PbModel

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section plog
variable [FfiSyntax]

def entId (e : EntryM) : entryID :=
  entryID.mk e.Term' e.Index'

/-- Contiguous indices from `b.index + 1`. The same statement as `LogIndicesOk`
(`InvRaftlog.lean`). -/
def PlogWf (b : entryID) (es : List EntryM) : Prop :=
  ∀ (k : Nat) (e : EntryM), es[k]? = some e →
    uint.Z e.Index' = uint.Z b.index' + ((k + 1 : Nat) : Int)

/-- `lastIndex()`, as an `Int`: `b.index + |es|`. -/
def plogLastIndexZ (b : entryID) (es : List EntryM) : Int :=
  uint.Z b.index' + (es.length : Int)

/-- `lastEntryID()`: the last entry's id, or `b` for an empty suffix. -/
def plogLast (b : entryID) (es : List EntryM) : entryID :=
  match es.getLast? with
  | some e => entId e
  | none => b

/-- `term(i)`: `some t` on `b.index ≤ i ≤ b.index + |es|`, `none` outside. Same shape
as `termAt` (`InvStorage.lean`) but total: `termAt` is only meaningful under its
range premise, this is meaningful everywhere, which is what `matchTerm`'s `bool`
result needs. -/
def plogTermAt (b : entryID) (es : List EntryM) (i : w64) : Option w64 :=
  if uint.Z i < uint.Z b.index' then none
  else if uint.Z i = uint.Z b.index' then some b.term'
  else (fun e : EntryM => e.Term') <$> es[(uint.Z i - uint.Z b.index' - 1).toNat]?

/-- `matchTerm(id)`: the log has `id.term` at `id.index`. -/
def PlogMatches (b : entryID) (es : List EntryM) (id : entryID) : Prop :=
  plogTermAt b es id.index' = some id.term'

instance PlogMatches_dec (b : entryID) (es : List EntryM) (id : entryID) :
    Decidable (PlogMatches b es id) := by
  unfold PlogMatches; infer_instance

/-- `findConflict(ents)`: the index of the first entry of `ents` the log does not have
(a different term there, or nothing there); `0` if the log has them all. -/
def plogFindConflict (b : entryID) (es : List EntryM) :
    List EntryM → w64
  | [] => W64 0
  | e :: ents' =>
      if PlogMatches b es (entId e) then plogFindConflict b es ents'
      else e.Index'

/-- The entries of the log from index `i` on (empty when `i` is past the end; the
whole suffix when `i ≤ b.index + 1`). -/
def plogFrom (b : entryID) (es : List EntryM) (i : w64) : List EntryM :=
  es.drop (uint.Z i - uint.Z b.index' - 1).toNat

/-- A prefix of the entries from `i` on, `i` past the base (2026-10-16, stage R8a): it ends within
the log, so `Next + |ents| ≤ lastIndex + 1` after `SentEntries` (`maybeSendAppend`). -/
theorem plogFrom_prefix_bound (b : entryID) (es es' : List EntryM) (i : w64)
    (H : es' <+: plogFrom b es i) (Hi : uint.Z b.index' + 1 ≤ uint.Z i)
    (Hi2 : uint.Z i ≤ plogLastIndexZ b es + 1) :
    uint.Z i + (es'.length : Int) ≤ plogLastIndexZ b es + 1 := by
  have Hl := H.length_le
  unfold plogFrom at Hl
  rw [List.length_drop] at Hl
  unfold plogLastIndexZ at *
  omega

/-- `unstable.truncateAndAppend(ents)` seen at the whole log: keep the entries below
`ents[0].Index`, then `ents`. Covers all three arms of the Go function (append in
place, replace the unstable suffix, truncate then append); for an empty batch nothing
changes. -/
def plogTruncateAppend (b : entryID) (es : List EntryM) (ents : List EntryM) :
    List EntryM :=
  match ents with
  | [] => es
  | e0 :: _ => es.take (uint.Z e0.Index' - uint.Z b.index' - 1).toNat ++ ents

/-- `raftLog.maybeAppend(a, committed)` without the commit: `none` when `a.prev` does
not match; otherwise the new last index `a.prev.index + |a.entries|` and the new entry
list -- unchanged if there is no conflict, else `truncateAndAppend` of the batch from
the conflict on (`a.entries[ci-offset:]` with `offset = a.prev.index + 1`). -/
def plogMaybeAppend (b : entryID) (es : List EntryM) (prev : entryID)
    (ents : List EntryM) : Option (w64 × List EntryM) :=
  if PlogMatches b es prev then
    let ci := plogFindConflict b es ents
    let es' :=
      if ci = W64 0 then es
      else plogTruncateAppend b es (ents.drop (uint.Z ci - uint.Z prev.index' - 1).toNat)
    some (W64 (uint.Z prev.index' + (ents.length : Int)), es')
  else none

/-- `commitTo(tocommit)`: never decreases. -/
def plogCommitTo (committed tocommit : w64) : w64 :=
  if uint.Z committed < uint.Z tocommit then tocommit else committed

theorem plogCommitTo_ge (c t : w64) : uint.Z c ≤ uint.Z (plogCommitTo c t) := by
  unfold plogCommitTo; split <;> omega

/-- `isUpToDate(their)`: `their` is at least as recent as our last entry. -/
def plogUpToDate (b : entryID) (es : List EntryM) (their : entryID) : Bool :=
  let l := plogLast b es
  decide (uint.Z l.term' < uint.Z their.term' ∨
          (their.term' = l.term' ∧ uint.Z l.index' ≤ uint.Z their.index'))

/-! ## Basic facts -/

theorem PlogWf_app (b : entryID) (es1 es2 : List EntryM) :
    PlogWf b (es1 ++ es2) ↔
    PlogWf b es1 ∧
    (∀ (k : Nat) (e : EntryM), es2[k]? = some e →
       uint.Z e.Index' = uint.Z b.index' + (es1.length : Int) + ((k + 1 : Nat) : Int)) := by
  unfold PlogWf
  constructor
  · intro H
    refine ⟨fun k e Hk => ?_, fun k e Hk => ?_⟩
    · apply H k e
      rw [List.getElem?_append_left]; exact Hk
      exact (List.getElem?_eq_some_iff.mp Hk).1
    · have := H (es1.length + k) e (by rw [List.getElem?_append_right (by omega)]; simpa using Hk)
      push_cast at this ⊢; omega
  · rintro ⟨H1, H2⟩ k e Hk
    by_cases Hlt : k < es1.length
    · rw [List.getElem?_append_left Hlt] at Hk; exact H1 k e Hk
    · rw [List.getElem?_append_right (by omega)] at Hk
      have := H2 _ _ Hk
      push_cast at this ⊢; omega

theorem PlogWf_take (b : entryID) (es : List EntryM) (n : Nat) :
    PlogWf b es → PlogWf b (es.take n) := by
  intro H k e Hk
  rw [List.getElem?_take] at Hk
  split at Hk
  · exact H k e Hk
  · cases Hk

theorem PlogWf_prefix (b : entryID) (es es' : List EntryM) :
    es <+: es' → PlogWf b es' → PlogWf b es := by
  rintro ⟨s, rfl⟩ H
  exact ((PlogWf_app _ _ _).1 H).1

/-- In range, `plogTermAt` is the term of the entry stored there. -/
theorem plogTermAt_lookup (b : entryID) (es : List EntryM) (i : w64) (k : Nat)
    (e : EntryM) :
    es[k]? = some e →
    uint.Z i = uint.Z b.index' + ((k + 1 : Nat) : Int) →
    plogTermAt b es i = some e.Term' := by
  intro Hk Hi
  unfold plogTermAt
  simp only [show ¬ (uint.Z i < uint.Z b.index') by omega,
    show ¬ (uint.Z i = uint.Z b.index') by omega, ↓reduceIte]
  have : (uint.Z i - uint.Z b.index' - 1).toNat = k := by omega
  rw [this, Hk]; rfl

theorem plogTermAt_base (b : entryID) (es : List EntryM) :
    plogTermAt b es b.index' = some b.term' := by
  unfold plogTermAt; simp

theorem plogTermAt_some_range (b : entryID) (es : List EntryM) (i t : w64) :
    plogTermAt b es i = some t →
    uint.Z b.index' ≤ uint.Z i ∧ uint.Z i ≤ plogLastIndexZ b es := by
  unfold plogTermAt plogLastIndexZ
  split
  · intro h; cases h
  split
  · intro _; omega
  cases Hk : es[(uint.Z i - uint.Z b.index' - 1).toNat]? with
  | none => intro h; cases h
  | some x =>
    intro _
    have := (List.getElem?_eq_some_iff.mp Hk).1
    omega

theorem plogTermAt_none_range (b : entryID) (es : List EntryM) (i : w64) :
    plogTermAt b es i = none ↔
    (uint.Z i < uint.Z b.index' ∨ plogLastIndexZ b es < uint.Z i) := by
  unfold plogTermAt plogLastIndexZ
  split
  · exact ⟨fun _ => .inl (by assumption), fun _ => rfl⟩
  split
  · constructor
    · intro h; cases h
    · intro h; omega
  cases Hk : es[(uint.Z i - uint.Z b.index' - 1).toNat]? with
  | none =>
    have := List.getElem?_eq_none_iff.mp Hk
    constructor
    · intro _; omega
    · intro _; rfl
  | some x =>
    have := (List.getElem?_eq_some_iff.mp Hk).1
    constructor
    · intro h; cases h
    · intro h; omega

/-- A well-formed log's entry at `i` has index `i`. -/
theorem PlogWf_lookup_index (b : entryID) (es : List EntryM) (k : Nat)
    (e : EntryM) :
    PlogWf b es → es[k]? = some e →
    uint.Z e.Index' = uint.Z b.index' + ((k + 1 : Nat) : Int) := by
  intro H Hk; exact H k e Hk

omit [FfiSyntax] in
theorem getLast?_some_getElem? {A : Type _} (l : List A) (e : A) (h : l.getLast? = some e) :
    l[l.length - 1]? = some e := by
  rw [List.getLast?_eq_getElem?] at h; exact h

/-- `plogLast` agrees with `plogLastIndexZ` on a well-formed log. -/
theorem plogLast_index (b : entryID) (es : List EntryM) :
    PlogWf b es → uint.Z (plogLast b es).index' = plogLastIndexZ b es := by
  intro Hwf
  unfold plogLast plogLastIndexZ
  cases Hl : es.getLast? with
  | some e =>
    have Hk := getLast?_some_getElem? es e Hl
    have := Hwf _ _ Hk
    have Hne : es.length ≠ 0 := by
      intro h; rw [List.length_eq_zero_iff] at h; subst h; cases Hl
    simp only [entId]
    push_cast at this; omega
  | none =>
    rw [List.getLast?_eq_none_iff] at Hl; subst Hl; simp

/-- The term at the last index is the last entry's term. -/
theorem plogTermAt_last (b : entryID) (es : List EntryM) :
    PlogWf b es →
    plogTermAt b es (plogLast b es).index' = some (plogLast b es).term' := by
  intro Hwf
  unfold plogLast
  cases Hl : es.getLast? with
  | some e =>
    have Hk := getLast?_some_getElem? es e Hl
    apply plogTermAt_lookup b es _ _ e Hk
    have := Hwf _ _ Hk
    have Hne : es.length ≠ 0 := by
      intro h; rw [List.length_eq_zero_iff] at h; subst h; cases Hl
    simp only [entId]
    push_cast at this ⊢; omega
  | none => exact plogTermAt_base b es

/-- `plogTruncateAppend` of a batch that continues the log is a plain append. -/
theorem plogTruncateAppend_cont (b : entryID) (es ents : List EntryM)
    (e0 : EntryM) :
    ents[0]? = some e0 →
    uint.Z e0.Index' = plogLastIndexZ b es + 1 →
    plogTruncateAppend b es ents = es ++ ents := by
  intro H0 Hidx
  unfold plogTruncateAppend
  cases ents with
  | nil => cases H0
  | cons e ents' =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at H0
    subst H0
    unfold plogLastIndexZ at Hidx
    have : (uint.Z e.Index' - uint.Z b.index' - 1).toNat = es.length := by omega
    dsimp only
    rw [this, List.take_of_length_le (Nat.le_refl _)]

/-- A well-formed log stays well-formed under `plogTruncateAppend` of a well-formed
batch starting inside or just after it. -/
theorem PlogWf_truncateAppend (b : entryID) (es ents : List EntryM)
    (e0 : EntryM) :
    PlogWf b es →
    ents[0]? = some e0 →
    (uint.Z b.index' < uint.Z e0.Index' ∧ uint.Z e0.Index' ≤ plogLastIndexZ b es + 1) →
    (∀ (k : Nat) (e : EntryM), ents[k]? = some e →
       uint.Z e.Index' = uint.Z e0.Index' + (k : Int)) →
    PlogWf b (plogTruncateAppend b es ents) := by
  intro Hwf H0 Hrange Hents
  unfold plogTruncateAppend
  cases ents with
  | nil => cases H0
  | cons e ents' =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at H0
    subst H0
    dsimp only
    rw [PlogWf_app]
    refine ⟨PlogWf_take _ _ _ Hwf, fun k e' Hk => ?_⟩
    have := Hents _ _ Hk
    rw [List.length_take]
    unfold plogLastIndexZ at Hrange
    have : min (uint.Z e.Index' - uint.Z b.index' - 1).toNat es.length =
        (uint.Z e.Index' - uint.Z b.index' - 1).toNat := by omega
    rw [this]
    push_cast; omega

end plog

end EtcdGrove
end Perennial
