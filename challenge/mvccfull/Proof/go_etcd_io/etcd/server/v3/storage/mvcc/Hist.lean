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

/-- The history of the committed log `log`, its revisions numbered from `i`. -/
def histOfFrom : Nat → Log → List HistItem
  | _, [] => []
  | i, cs :: log => (evsOfRev i cs).map .ev ++ [.commit] ++ histOfFrom (i + 1) log

/-- The history of the committed log `log`. -/
def histOf (log : Log) : List HistItem := histOfFrom 0 log

/-- The history of `ilog` committed and the changes `pend` of the pending revision put. -/
def histShape (ilog : Log) (pend : List Change) : List HistItem :=
  histOf ilog ++ (evsOfRev ilog.length pend).map .ev

/-! ### A reader's certified log, as a prefix of the history -/

/-! ### The history determines the log -/

/-! ### A reader's answer is stable under later events -/

/-! ### The writer: the key's index is not empty, its `modified` is below the new revision -/

/-! ### Finding a key in a sorted index -/

/-! ### The tree's entries: finding and inserting by key -/

/-- An entry of the index: the key index's pointer, its key and its model (`InvIndex.lean`). -/
abbrev IdxEntry := Loc × GoString × KeyIndex

def idxOfEntries (L : List IdxEntry) : IndexM := L.map fun z => (z.2.1, z.2.2)

def itemsOfEntries (L : List IdxEntry) : List (Loc × GoString) := L.map fun z => (z.1, z.2.1)

/-- The items' order: by key (`keyIndex.Less`). -/
def kiItemLess (a b : Loc × GoString) : Prop := go.GoStringLt a.2 b.2

/-! ### Range reads: the keys in `[k, e)` with their answers -/

/-! ### What `unsafeVisit` visits: the entries at or above `k`, until one at or above `e` -/

/-! ### `Revisions`, `CountRevisions`, `Range`: the model -/

/-! ### The visitor's accumulation: the answers of a prefix of the visited entries -/

end mvcc
end EtcdGrove
end Perennial
