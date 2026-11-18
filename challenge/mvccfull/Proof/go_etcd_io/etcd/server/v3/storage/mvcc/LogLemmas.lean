/-
The index as a function of the log (`Model.lean`), key by key: the index built from the events
(`indexOf`) holds, for every key, the key index built from that key's events alone
(`kiOfKey`, `indexOf_rep`); and what that key index answers at a revision is the key-value of
the state at that revision (`kiGet_kiOfKey`, the model's main theorem). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ### The index, key by key -/

/-- One event applied to a key's index: `idxApply` seen from the key. A tombstone of a key
whose last generation is empty (or that has no index: `kiEmpty`) changes nothing. -/
def kiApply (ki : KeyIndex) (ev : Ev) : KeyIndex :=
  if ev.tomb then (if kiLastEmpty ki then ki else kiTombstone ki ev.rev) else kiPut ki ev.rev

/-- The key index of `k` after the events `evs`: those of `k`, applied to the empty index. -/
def kiOfKey (evs : List Ev) (k : GoString) : KeyIndex :=
  (evs.filter fun ev => decide (ev.key = k)).foldl kiApply kiEmpty

/-! ### The state: `findKey` through a put and a delete -/

/-! ### The log: states and events of an appended revision -/

/-! ### Key and value lengths (2026-10-30, `notes/keylen.md`; values 2026-10-31,
`notes/vallen.md`) -/

/-! ### A read at the top of a key index -/

/-! ### The main theorem: what the key index answers is the state's key-value -/

/-- The well-formedness of a log the induction carries: revision 0 (if any) is empty, and
every delete is of a key present at that point. `LogWf` implies it, and it holds of every
prefix. -/
def LogWf' (log : Log) : Prop :=
  (log ≠ [] → log[0]? = some []) ∧
  ∀ (r : Nat) (cs : List Change) (i : Nat) (k : GoString), log[r]? = some cs →
    cs[i]? = some (.del k) →
    (findKey k (applyChanges (W64 r) (stateAt log (r - 1)) (cs.take i))).isSome

end mvcc
end EtcdGrove
end Perennial
