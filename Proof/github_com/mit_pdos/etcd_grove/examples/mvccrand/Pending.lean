/-
The writer's pending transaction (`pending`, `examples/mvccrand/mvccrand.go`): its model and its
ownership. Lean-first (no Rocq counterpart).

A `pending` is the model of the write transaction the writer is running: the revision it writes
(`rev`), the state it makes (`st`, a map the writer owns: a copy of the last revision's, then
changed), and its changes so far (`changes`), in order. `PendM` is that as one record; `put` and
`del` are what `pending.put`/`pending.del` do to it (the tester's model of mvcc's put and range
delete: a put keeps the create revision and bumps the version of a key present, else creates it at
`rev`, version 1; a delete removes the range's present keys, in the tester's key order, which is
`matchKeys`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand

section model
variable [GooseExts]

/-- A pending transaction's model: its revision, its state, its changes. -/
structure PendM where
  rev : w64
  st : GMap GoString kvRec
  chs : List change

/-- The key-value a put of `v` (lease `l`) at revision `rev` gives `k` in state `M`. -/
def putRec (M : GMap GoString kvRec) (rev : w64) (k v : GoString) (l : w64) : kvRec :=
  match M !! k with
  | some e => { val' := v, create' := e.create', mod' := rev, ver' := e.ver' + W64 1, lease' := l }
  | none => { val' := v, create' := rev, mod' := rev, ver' := W64 1, lease' := l }

/-- A deletion's change of key `k`. -/
def delChange (k : GoString) : change := { del' := true, key' := k, kv' := zeroValDef }

/-- `p.put(k, v, l)`. -/
def PendM.put (P : PendM) (k v : GoString) (l : w64) : PendM :=
  { P with st := <[k := putRec P.st P.rev k v l]> P.st,
           chs := P.chs ++ [{ del' := false, key' := k, kv' := putRec P.st P.rev k v l }] }

/-- The keys `p.del(key, end)` deletes: the tester's keys, in order, present and in the range. -/
abbrev PendM.delKeys (P : PendM) (endNil : Bool) (kk e : GoString) : List GoString :=
  matchKeys P.st endNil kk e

/-- Deleting the keys `ks` from a map. -/
def delAll (ks : List GoString) (M : GMap GoString kvRec) : GMap GoString kvRec :=
  ks.foldl (fun m k => GMap.delete k m) M

/-- `p.del(key, end)`. -/
def PendM.del (P : PendM) (endNil : Bool) (kk e : GoString) : PendM :=
  { P with st := delAll (P.delKeys endNil kk e) P.st,
           chs := P.chs ++ (P.delKeys endNil kk e).map delChange }

theorem delAll_lookup (ks : List GoString) (M : GMap GoString kvRec) (x : GoString) :
    delAll ks M !! x = if x ∈ ks then none else M !! x := by
  induction ks generalizing M with
  | nil => simp [delAll]
  | cons k ks ih =>
    unfold delAll at ih ⊢
    rw [List.foldl_cons, ih]
    by_cases hx : x ∈ ks
    · simp [hx]
    · by_cases hk : k = x
      · subst hk; simp
      · simp only [hx, ↓reduceIte, List.mem_cons, Ne.symm hk, false_or]
        exact GMap.lookup_delete_ne _ hk

theorem delAll_append (ks ks' : List GoString) (M : GMap GoString kvRec) :
    delAll (ks ++ ks') M = delAll ks' (delAll ks M) := by
  unfold delAll; rw [List.foldl_append]

end model

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- **The pending transaction at `p` is `P`**: its struct, its state's map and its changes'
slice, all owned. -/
def ownPending (p : Loc) (P : PendM) : IProp GF :=
  iprop(∃ pv : pending, p ↦ pv ∗ ⌜pv.rev' = P.rev⌝ ∗ pv.st' ↦$ P.st ∗ pv.changes' ↦* P.chs ∗
    ownSliceCap change pv.changes' (DFrac.own 1))

end own

end mvccrand
end EtcdGrove
end Perennial
