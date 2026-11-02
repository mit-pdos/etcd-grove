/-
Lean-first (no Rocq counterpart).

# The applier's frozen entries (`frozenTo`), entry by entry (2026-10-29, kvreconf's `run`)

`frozenTo γs c D` holds the delivered log `D`'s entries above `c` read-only in the storage. A
snapshot or a compaction at index `i` in `(c, |D|]` takes the one entry there (`frozenTo_at`), whose
term is `D`'s at `i` (the entry at position `i - 1`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The Go entry at position `k` of the log entries `ce` handed out after `base`. -/
theorem kvr_toEntries_get [GooseExts] (ce : List LogEntry) (base k : Nat) (en : LogEntry)
    (h : ce[k]? = some en) :
    (LogEntry.toEntries ce base)[k]? = some (en.toEntryM (W64 (base + k + 1))) := by
  unfold LogEntry.toEntries; rw [List.getElem?_mapIdx, h]; rfl

theorem kvr_toEntries_length [GooseExts] (ce : List LogEntry) (base : Nat) :
    (LogEntry.toEntries ce base).length = ce.length := by
  unfold LogEntry.toEntries; simp

theorem kvr_toEntries_append [GooseExts] (a b : List LogEntry) (base : Nat) :
    LogEntry.toEntries (a ++ b) base =
      LogEntry.toEntries a base ++ LogEntry.toEntries b (base + a.length) := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < a.length
  · rw [List.getElem?_append_left (by rw [kvr_toEntries_length]; exact hk)]
    obtain ⟨x, hx⟩ : ∃ x, a[k]? = some x := ⟨a[k], List.getElem?_eq_getElem hk⟩
    rw [kvr_toEntries_get a base k x hx,
      kvr_toEntries_get (a ++ b) base k x (by rw [List.getElem?_append_left hk]; exact hx)]
  · have hk' : a.length ≤ k := Nat.le_of_not_lt hk
    rw [List.getElem?_append_right (by rw [kvr_toEntries_length]; exact hk'),
      kvr_toEntries_length]
    cases hb : b[k - a.length]? with
    | none =>
      have h1 : (a ++ b)[k]? = none := by rw [List.getElem?_append_right hk']; exact hb
      have h2 : (LogEntry.toEntries (a ++ b) base)[k]? = none := by
        unfold LogEntry.toEntries; rw [List.getElem?_mapIdx, h1]; rfl
      have h3 : (LogEntry.toEntries b (base + a.length))[k - a.length]? = none := by
        unfold LogEntry.toEntries; rw [List.getElem?_mapIdx, hb]; rfl
      rw [h2, h3]
    | some x =>
      rw [kvr_toEntries_get (a ++ b) base k x (by rw [List.getElem?_append_right hk']; exact hb),
        kvr_toEntries_get b (base + a.length) (k - a.length) x hb]
      congr 3
      omega

section frozen
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- One entry of a range. -/
theorem memLog_elem (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) (j : Nat)
    (e : EntryM) (h : es[j]? = some e) :
    memLog (GF := GF) γs k dq es ⊢ memLog γs (k + j) dq [e] := by
  have hj : j < es.length := by
    rcases Nat.lt_or_ge j es.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  have he : es[j] = e := by
    rw [List.getElem?_eq_getElem hj] at h; cases h; rfl
  have hes : es = es.take j ++ ([e] ++ es.drop (j + 1)) := by
    refine (List.take_append_drop j es).symm.trans ?_
    rw [List.drop_eq_getElem_cons hj, he]; rfl
  have hl : (es.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  rw [hes]
  iintro H
  icases (memLog_app γs k dq _ _).1 $$ H with ⟨-, H⟩
  icases (memLog_app γs _ dq _ _).1 $$ H with ⟨H, -⟩
  rw [hl]
  iexact H

/-- **The frozen entry at `i`** in `(c, |D|]`, with `D`'s term there. -/
theorem frozenTo_at (γs : MemStorNames) (c : Nat) (D : List LogEntry) (i : Nat)
    (h1 : c < i) (h2 : i ≤ D.length) :
    frozenTo (GF := GF) γs c D ⊢ ∃ e : EntryM, memLog γs i DFrac.discard [e] ∗
      ⌜∀ x, D[i - 1]? = some x → e = x.toEntryM (W64 i)⌝ := by
  unfold frozenTo
  have hx : i - 1 < D.length := by omega
  have hD : D[i - 1]? = some D[i - 1] := List.getElem?_eq_getElem hx
  have hg := kvr_toEntries_get D 0 (i - 1) D[i - 1] hD
  have hg0 : ((LogEntry.toEntries D 0).drop c)[i - 1 - c]? = (LogEntry.toEntries D 0)[i - 1]? := by
    rw [List.getElem?_drop, show c + (i - 1 - c) = i - 1 by omega]
  have hg' : ((LogEntry.toEntries D 0).drop c)[i - 1 - c]? = some (D[i - 1].toEntryM (W64 i)) := by
    rw [hg0, hg]; congr 3; push_cast; omega
  iintro #H
  ihave H' := memLog_elem γs (c + 1) DFrac.discard _ (i - 1 - c) _ hg' $$ H
  rw [show c + 1 + (i - 1 - c) = i by omega]
  iexists D[i - 1].toEntryM (W64 i)
  iframe H'
  ipureintro
  intro x hxx
  rw [hD] at hxx; cases hxx; rfl

end frozen

end kvreconf
end EtcdGrove
end Perennial
