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

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc

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

/-- `pending.del`'s step on one key: deleted from the state, a delete appended to the changes. -/
def PendM.delOne (P : PendM) (k : GoString) : PendM :=
  { P with st := GMap.delete k P.st, chs := P.chs ++ [delChange k] }

/-- One change applied to the tester's pending model (a put as `pending.put`). -/
def PendM.step (P : PendM) : Change → PendM
  | .put k v l => P.put k v l
  | .del k => P.delOne k

/-- **The tester's model after mvcc's changes `cs` of revision `rev` from the state `M`.** -/
def pendOf (M : GMap GoString kvRec) (rev : w64) (cs : List Change) : PendM :=
  cs.foldl PendM.step ⟨rev, M, []⟩

theorem pendOf_nil (M : GMap GoString kvRec) (rev : w64) : pendOf M rev [] = ⟨rev, M, []⟩ := rfl

theorem pendOf_append (M : GMap GoString kvRec) (rev : w64) (cs cs' : List Change) :
    pendOf M rev (cs ++ cs') = cs'.foldl PendM.step (pendOf M rev cs) := by
  unfold pendOf; rw [List.foldl_append]

theorem pendOf_put (M : GMap GoString kvRec) (rev : w64) (cs : List Change) (k v : GoString)
    (l : w64) : pendOf M rev (cs ++ [.put k v l]) = (pendOf M rev cs).put k v l := by
  rw [pendOf_append]; rfl

theorem foldl_step_rev (ks : List Change) (P : PendM) : (ks.foldl PendM.step P).rev = P.rev := by
  induction ks generalizing P with
  | nil => rfl
  | cons c cs ih =>
    rw [List.foldl_cons, ih]
    cases c <;> rfl

theorem pendOf_rev (M : GMap GoString kvRec) (rev : w64) (cs : List Change) :
    (pendOf M rev cs).rev = rev := by
  unfold pendOf; rw [foldl_step_rev]

theorem foldl_step_chs_length (ks : List Change) (P : PendM) :
    (ks.foldl PendM.step P).chs.length = P.chs.length + ks.length := by
  induction ks generalizing P with
  | nil => rfl
  | cons c cs ih =>
    rw [List.foldl_cons, ih]
    cases c <;> simp [PendM.step, PendM.put, PendM.delOne] <;> omega

theorem pendOf_chs_length (M : GMap GoString kvRec) (rev : w64) (cs : List Change) :
    (pendOf M rev cs).chs.length = cs.length := by
  unfold pendOf; rw [foldl_step_chs_length]; simp

theorem pendOf_chs_nil_iff (M : GMap GoString kvRec) (rev : w64) (cs : List Change) :
    (pendOf M rev cs).chs = [] ↔ cs = [] := by
  rw [← List.length_eq_zero_iff, pendOf_chs_length, List.length_eq_zero_iff]

theorem delOne_foldl (ks : List GoString) (Q : PendM) :
    ({ Q with st := delAll ks Q.st, chs := Q.chs ++ ks.map delChange } : PendM) =
      (ks.map Change.del).foldl PendM.step Q := by
  induction ks generalizing Q with
  | nil => simp [delAll]
  | cons k ks ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [← ih]
    simp only [PendM.step, PendM.delOne, delAll, List.foldl_cons, List.append_assoc,
      List.cons_append, List.nil_append]

/-- `pending.del` is its deletes one key at a time, in key order. -/
theorem PendM.del_eq_foldl (P : PendM) (endNil : Bool) (kk e : GoString) :
    P.del endNil kk e = ((P.delKeys endNil kk e).map Change.del).foldl PendM.step P := by
  unfold PendM.del; exact delOne_foldl _ P

end model

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- The tester's states: the maps `ms` hold `Ms`, at the fractions `dqs`. -/
def statesAt (ms : List GoMap) (Ms : List (GMap GoString kvRec)) (dqs : List DFrac) : IProp GF :=
  iprop(⌜ms.length = Ms.length ∧ Ms.length = dqs.length⌝ ∗
    [∗list] x ∈ ms.zip (Ms.zip dqs), x.1 ↦${x.2.2} x.2.1)

/-- **The pending transaction at `p` is `P`**: its struct, its state's map and its changes'
slice, all owned. -/
def ownPending (p : Loc) (P : PendM) : IProp GF :=
  iprop(∃ pv : pending, p ↦ pv ∗ ⌜pv.rev' = P.rev⌝ ∗ pv.st' ↦$ P.st ∗ pv.changes' ↦* P.chs ∗
    ownSliceCap change pv.changes' (DFrac.own 1))

end own

end mvccrand
end EtcdGrove
end Perennial
