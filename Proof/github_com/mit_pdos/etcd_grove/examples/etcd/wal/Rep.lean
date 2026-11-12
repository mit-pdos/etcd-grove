/-
Lean-first (no Rocq counterpart).

# The tester's Go values as its Lean records (WAL W4c step 3)

The representation predicates the specs of the tester's functions are written in:

* an entry slice is read-only once built (`↦*□`): an operation's entries are shared by every copy
  of the operation (`copyOps` copies the slice headers);
* an operation (`walOp`) is its fields and its entries (`opRep`, persistent);
* an operation slice is read-only too (`opsRep`): the candidates' histories and the images are
  never written once built, and the history `since` is only appended to (the append writes past
  the persistent elements, into the capacity the oracle owns: `wp_slice_append_persistent`);
* the oracle (`oracleRep`) owns its candidate slice (whose bounds are written in place) and the
  capacities of the slices it appends to.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.wal

section pure
variable [GooseExts]

instance THs_decEq : DecidableEq THs := fun a b =>
  decidable_of_iff (a.term' = b.term' ∧ a.vote' = b.vote' ∧ a.commit' = b.commit')
    (by cases a; cases b; simp)

instance TEnt_decEq : DecidableEq TEnt := fun a b =>
  decidable_of_iff (a.index' = b.index' ∧ a.term' = b.term' ∧ a.size' = b.size' ∧ a.salt' = b.salt')
    (by cases a; cases b; simp)

end pure

section rep
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- A postcondition at a value computed in the proof: `HΦ` at any `y` equal to the spec's `x` (so
each branch of a proof returns its own expression of the value and proves it equal). -/
theorem ret_gen {V : Type} (Φ : val → IProp GF) (x : V) (P : IProp GF) :
    (P -∗ Φ #x) ⊢ ∀ y : V, ⌜y = x⌝ ∗ P -∗ Φ #y := by
  iintro H %y ⟨%hy, HP⟩
  subst hy
  iapply H $$ HP

/-- The Go operation `v` is `o`: its fields, and its entries (read-only). -/
def opRep (v : walOp) (o : TOp) : IProp GF :=
  iprop(⌜v.snap' = o.snap ∧ v.hs' = o.hs ∧ v.idx' = o.idx ∧ v.term' = o.term⌝ ∗ v.ents' ↦*□ o.ents)

instance opRep_persistent (v : walOp) (o : TOp) : Persistent (opRep (GF := GF) v o) := by
  unfold opRep; infer_instance

/-- The Go values `vs` are the operations `h`, element by element. -/
def opsElems (vs : List walOp) (h : List TOp) : IProp GF :=
  iprop(⌜vs.length = h.length⌝ ∗ □ ∀ (i : Nat) (v : walOp) (o : TOp),
    ⌜vs[i]? = some v ∧ h[i]? = some o⌝ -∗ opRep v o)

instance opsElems_persistent (vs : List walOp) (h : List TOp) :
    Persistent (opsElems (GF := GF) vs h) := by
  unfold opsElems; infer_instance

/-- The operation slice `s` is `h` (read-only). -/
def opsRep (s : GoSlice) (h : List TOp) : IProp GF :=
  iprop(∃ vs : List walOp, s ↦*□ vs ∗ opsElems vs h)

instance opsRep_persistent (s : GoSlice) (h : List TOp) : Persistent (opsRep (GF := GF) s h) := by
  unfold opsRep; infer_instance

/-- The Go candidate `v` is `c`. -/
def candRep (v : cand) (c : TCand) : IProp GF :=
  iprop(⌜v.unl' = c.unl ∧ v.pur' = c.pur⌝ ∗ opsRep v.h' c.h)

instance candRep_persistent (v : cand) (c : TCand) : Persistent (candRep (GF := GF) v c) := by
  unfold candRep; infer_instance

/-- The Go candidates `vs` are `cs`, element by element. -/
def candsElems (vs : List cand) (cs : List TCand) : IProp GF :=
  iprop(⌜vs.length = cs.length⌝ ∗ □ ∀ (i : Nat) (v : cand) (c : TCand),
    ⌜vs[i]? = some v ∧ cs[i]? = some c⌝ -∗ candRep v c)

instance candsElems_persistent (vs : List cand) (cs : List TCand) :
    Persistent (candsElems (GF := GF) vs cs) := by
  unfold candsElems; infer_instance

/-- The candidate slice `s` is `cs`, owned with its capacity (its elements' bounds are written in
place, and it is appended to). -/
def candsOwn (s : GoSlice) (cs : List TCand) : IProp GF :=
  iprop(∃ vs : List cand, s ↦* vs ∗ ownSliceCap cand s (DFrac.own 1) ∗ candsElems vs cs)

/-- The Go contents `v` are `c` (the entries read-only). -/
def contentsRep (v : contents) (c : TContents) : IProp GF :=
  iprop(⌜v.hs' = c.hs ∧ v.baseIdx' = c.baseIdx ∧ v.baseTerm' = c.baseTerm⌝ ∗ v.ents' ↦*□ c.ents)

instance contentsRep_persistent (v : contents) (c : TContents) :
    Persistent (contentsRep (GF := GF) v c) := by
  unfold contentsRep; infer_instance

/-- **The Go oracle `v` is `o`**: the candidates owned, `since` read-only with its capacity, the
pending opens read-only with their capacity. -/
def oracleRep (v : oracle) (o : TOracle) : IProp GF :=
  iprop(⌜v.created' = o.created ∧ v.synced' = o.synced ∧ v.lastHS' = o.lastHS⌝ ∗
    candsOwn v.cands' o.cands ∗
    opsRep v.since' o.since ∗ ownSliceCap walOp v.since' (DFrac.own 1) ∗
    v.opens' ↦*□ o.opens ∗ ownSliceCap w64 v.opens' (DFrac.own 1))

end rep

end etcd_wal
end EtcdGrove
end Perennial
