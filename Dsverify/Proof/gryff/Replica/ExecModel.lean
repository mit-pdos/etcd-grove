/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Replica/ExecModel.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

What the replica's executor gives the protocol (hub request H3): the committed instances'
dependency graph (`depE C`, from the committed attributes `C`, U4's `InstAttrs`), the order a
component is executed in (`sortedBy`: `(seq, leader, slot)`, G4's `nodeArray.Less`), a valid
sequence of executed instances (`chainOk`: components in turn, each `sccStep` after the earlier
ones, sorted), and the next entry's result (`chainCur`, `nextEntry`: the executor's `PrevValTag`
rule with G1).
-/
module

public import Dsverify.Proof.gryff.Replica.Tarjan
public import Dsverify.Proof.gryff.Proto.Inv
public import Batteries.Data.List.Perm
public import Dsverify.Proof.gryff.Proto.Epaxos

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica

open proto

/-- `u` depends on `w`: `w = (q, i)` is in the range of `u`'s committed deps (`i ≤ deps[q]`,
`q` one of the three replicas). -/
def depE (C : GMap Node InstAttrs) (u w : Node) : Prop :=
  ∃ a, C.lookup u = some a ∧ 0 ≤ w.1 ∧ w.1 < 3 ∧ 0 ≤ w.2 ∧ w.2 ≤ a.deps.getD w.1.toNat (-1)

/-- The lexicographic order of `(seq, leader, slot)` (G4: `nodeArray.Less`). -/
def keyLt (a b : Int × Int × Int) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))

/-- An instance's sort key. -/
def keyOf (C : GMap Node InstAttrs) (n : Node) : Int × Int × Int :=
  ((C.lookup n).elim 0 InstAttrs.seq, n.1, n.2)

/-- A component's execution order. -/
def sortedBy (C : GMap Node InstAttrs) (Ls : List Node) : Prop :=
  Ls.Pairwise (fun a b => keyLt (keyOf C a) (keyOf C b))

/-- `Ls`, executed after `X`, is a component of committed instances, in its order. -/
def batchOk (C : GMap Node InstAttrs) (X Ls : List Node) : Prop :=
  ∃ L, sccStep (depE C) X L ∧ Ls.Perm L ∧ sortedBy C Ls ∧ ∀ u ∈ Ls, (C.lookup u).isSome

/-- A sequence of whole components. -/
inductive chainOk (C : GMap Node InstAttrs) : List Node → Prop
  | nil : chainOk C []
  | snoc (X Ls : List Node) : chainOk C X → batchOk C X Ls → chainOk C (X ++ Ls)

/-- A replica's executed instances: a prefix of a sequence of whole components. -/
def idsOk (C : GMap Node InstAttrs) (ids : List Node) : Prop :=
  ∃ Y, chainOk C Y ∧ ids <+: Y

/-- The value and tag the next RMW applies to: its base, or the previous result if it is newer
(`epaxos-exec.go`: `if !ok || w.Base.T.GreaterThan(pvt.T)`). -/
def chainCur (prev : Option (Int × PTag)) (base : Int × PTag) : Int × PTag :=
  match prev with
  | none => base
  | some p => if tagLt p.2 base.2 then base else p

/-- The entry of executing instance `n` with attributes `a` after the result `prev`. -/
def nextEntry (prev : Option (Int × PTag)) (n : Node) (a : InstAttrs) : ExecEntry :=
  let cur := chainCur prev a.base
  { inst := n, base := a.base, old := a.old, new := a.new,
    res := (casStep a.old a.new cur.1, rmwTag cur.2) }

/-- The last result of a sequence of entries. -/
def lastRes (ents : List ExecEntry) : Option (Int × PTag) := ents.getLast?.map ExecEntry.res

/-- Entries built one by one by `nextEntry` form an `execOk` chain. -/
theorem execOk_snoc (ents : List ExecEntry) (n : Node) (a : InstAttrs)
    (h : execOk none ents) : execOk none (ents ++ [nextEntry (lastRes ents) n a]) := by
  suffices ∀ prev, execOk prev ents →
      execOk prev (ents ++ [nextEntry ((lastRes ents).or prev) n a]) by
    have := this none h; simpa using this
  clear h
  induction ents with
  | nil =>
    intro prev _
    cases prev <;> simp [execOk, nextEntry, chainCur, lastRes]
  | cons e es ih =>
    intro prev h
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1, ?_⟩
    have := ih (some e.res) h2
    cases es with
    | nil => simpa [lastRes] using this
    | cons e' es' =>
      have hl : lastRes (e :: e' :: es') = lastRes (e' :: es') := by
        simp [lastRes, List.getLast?_cons_cons]
      rw [hl]
      have hor : ((lastRes (e' :: es')).or (some e.res)) = (lastRes (e' :: es')).or prev := by
        simp [lastRes, List.getLast?_cons]
      rw [← hor]; exact this

/-! ## Growth of the committed attributes -/

/-- `C'` extends `C`. -/
def CSub (C C' : GMap Node InstAttrs) : Prop := ∀ n a, C.lookup n = some a → C'.lookup n = some a

theorem CSub.refl (C : GMap Node InstAttrs) : CSub C C := fun _ _ h => h
theorem CSub.trans {C1 C2 C3 : GMap Node InstAttrs} (h1 : CSub C1 C2) (h2 : CSub C2 C3) :
    CSub C1 C3 := fun n a h => h2 n a (h1 n a h)

theorem depE_mono {C C' : GMap Node InstAttrs} (h : CSub C C') {u w : Node}
    (hE : depE C u w) : depE C' u w := by
  obtain ⟨a, ha, h1⟩ := hE; exact ⟨a, h u a ha, h1⟩

theorem depE_of_mono {C C' : GMap Node InstAttrs} (h : CSub C C') {u w : Node}
    (hu : (C.lookup u).isSome) (hE : depE C' u w) : depE C u w := by
  obtain ⟨a, ha, h1⟩ := hE
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hu
  have := h u b hb; rw [ha] at this; cases this
  exact ⟨a, hb, h1⟩

theorem keyOf_mono {C C' : GMap Node InstAttrs} (h : CSub C C') {n : Node}
    (hn : (C.lookup n).isSome) : keyOf C' n = keyOf C n := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hn
  simp [keyOf, hb, h n b hb]

theorem sccStep_mono {C C' : GMap Node InstAttrs} (h : CSub C C') {X L : List Node}
    (hL : ∀ u ∈ L, (C.lookup u).isSome) (hs : sccStep (depE C) X L) :
    sccStep (depE C') X L := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  exact ⟨h1, h2, h3, fun u hu w hw => h4 u hu w (depE_of_mono h (hL u hu) hw),
    fun u hu w hw => (h5 u hu w hw).mono (fun _ _ => depE_mono h)⟩

theorem batchOk_mono {C C' : GMap Node InstAttrs} (h : CSub C C') {X Ls : List Node}
    (hL : ∀ u ∈ Ls, (C.lookup u).isSome) (hb : batchOk C X Ls) : batchOk C' X Ls := by
  obtain ⟨L, hs, hp, hsort, hcm⟩ := hb
  refine ⟨L, sccStep_mono h (fun u hu => hL u (hp.mem_iff.2 hu)) hs, hp, ?_, fun u hu => ?_⟩
  · unfold sortedBy at hsort ⊢
    refine hsort.imp_of_mem ?_
    intro a b ha hb' hab
    rw [keyOf_mono h (hL a ha), keyOf_mono h (hL b hb')]; exact hab
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (hcm u hu)
    rw [h u a ha]; rfl
theorem chainOk_mono {C C' : GMap Node InstAttrs} (h : CSub C C') {Y : List Node}
    (hY : ∀ u ∈ Y, (C.lookup u).isSome) (hc : chainOk C Y) : chainOk C' Y := by
  induction hc with
  | nil => exact .nil
  | snoc X Ls _ hb ih =>
    exact .snoc X Ls (ih (fun u hu => hY u (List.mem_append_left _ hu)))
      (batchOk_mono h (fun u hu => hY u (List.mem_append_right _ hu)) hb)

/-- The next instance of a component being executed extends a valid sequence. -/
theorem idsOk_step {C : GMap Node InstAttrs} {X0 Ls : List Node} (hc : chainOk C X0)
    (hb : batchOk C X0 Ls) (j : Nat) (n : Node) (hj : Ls[j]? = some n) :
    idsOk C (X0 ++ Ls.take j ++ [n]) := by
  refine ⟨X0 ++ Ls, .snoc X0 Ls hc hb, ?_⟩
  rw [List.append_assoc]
  refine (List.prefix_append_right_inj X0).2 ?_
  have : Ls.take j ++ [n] = Ls.take (j + 1) := by
    rw [List.take_add_one, hj]; rfl
  rw [this]; exact List.take_prefix _ _

/-! ## The instance space's box (bounds the search's counter) -/

/-- The instances of the instance space: three rows of `2^21` slots. -/
def inBox (n : Node) : Prop := 0 ≤ n.1 ∧ n.1 < 3 ∧ 0 ≤ n.2 ∧ n.2 < 2 * 1024 * 1024

def boxList : List Node :=
  (List.range 3).flatMap (fun (q : Nat) =>
    (List.range (2 * 1024 * 1024)).map fun (i : Nat) => ((q : Int), (i : Int)))

theorem boxList_length : boxList.length = 3 * (2 * 1024 * 1024) := by
  simp only [boxList, List.length_flatMap, List.length_map, List.length_range]
  rfl

theorem mem_boxList {n : Node} (h : inBox n) : n ∈ boxList := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [boxList, List.mem_flatMap, List.mem_range, List.mem_map]
  refine ⟨n.1.toNat, by omega, n.2.toNat, by omega, ?_⟩
  obtain ⟨a, b⟩ := n
  simp only at h1 h2 h3 h4 ⊢
  ext <;> simp <;> omega

/-- A list of distinct instances of the box has at most `3 * 2^21` elements. -/
theorem box_nodup_length {vis : List Node} (hnd : vis.Nodup) (hb : ∀ n ∈ vis, inBox n) :
    vis.length ≤ 3 * (2 * 1024 * 1024) := by
  rw [← boxList_length]
  exact (List.subperm_of_subset hnd (fun n hn => mem_boxList (hb n hn))).length_le

/-! ## The bridge to the protocol's agreement theorem (`GryffProof/Proto/Epaxos.lean`, U4's) -/

/-- The committed attributes as the agreement theorem's functions. -/
def depsOf (C : GMap Node InstAttrs) (x : Node) : List Int := (C.lookup x).elim [] InstAttrs.deps
def seqOf (C : GMap Node InstAttrs) (x : Node) : Int := (C.lookup x).elim 0 InstAttrs.seq

theorem depE_eq_gdep (C : GMap Node InstAttrs) : depE C = epaxos.gdep (depsOf C) := by
  funext x y
  apply propext
  unfold depE epaxos.gdep depsOf
  cases hx : C.lookup x with
  | none =>
    simp only [Option.elim, List.getD_nil]
    constructor
    · rintro ⟨a, ha, _⟩; cases ha
    · intro h; omega
  | some a =>
    simp only [Option.elim]
    constructor
    · rintro ⟨a', ha', h⟩; cases ha'; exact h
    · intro h; exact ⟨a, rfl, h⟩

theorem keyLt_eq_gkeyLt (C : GMap Node InstAttrs) (x y : Node) :
    keyLt (keyOf C x) (keyOf C y) ↔ epaxos.gkeyLt (seqOf C) x y := by
  unfold keyLt keyOf epaxos.gkeyLt seqOf; exact Iff.rfl

/-- The executed instances are closed under dependencies. -/
def XClosed (E : Node → Node → Prop) (X : List Node) : Prop := ∀ x ∈ X, ∀ y, E x y → y ∈ X

theorem chainOk_closed {C : GMap Node InstAttrs} {Y : List Node} (h : chainOk C Y) :
    XClosed (depE C) Y := by
  induction h with
  | nil => intro x hx; cases hx
  | snoc X Ls _ hb ih =>
    obtain ⟨L, ⟨_, _, _, hcl, _⟩, hp, _, _⟩ := hb
    intro x hx y hy
    rcases List.mem_append.1 hx with hx | hx
    · exact List.mem_append_left _ (ih x hx y hy)
    · rcases hcl x (hp.mem_iff.1 hx) y hy with h1 | h1
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (hp.mem_iff.2 h1)

theorem reach_closed {E : Node → Node → Prop} {X : List Node} (hX : XClosed E X) {b c : Node}
    (h : Reach E b c) (hb : b ∈ X) : c ∈ X := by
  induction h with
  | refl => exact hb
  | step a b' c hab _ ih => exact ih (hX a hb b' hab)

/-- In a component popped after closed executed instances, paths between members stay inside. -/
theorem reachIn_of_scc {E : Node → Node → Prop} {X L : List Node} (hs : sccStep E X L)
    (hX : XClosed E X) {u w : Node} (h : Reach E u w) (hu : u ∈ L) (hw : w ∈ L) :
    epaxos.ReachIn E L u w := by
  obtain ⟨_, _, hnX, hcl, _⟩ := hs
  induction h with
  | refl => exact .refl _
  | step a b c hab hbc ih =>
    rcases hcl a hu b hab with hbX | hbL
    · exact absurd (reach_closed hX hbc hbX) (hnX c hw)
    · exact .step hab hbL (ih hbL hw)

theorem reachIn_perm {E : Node → Node → Prop} {L L' : List Node} (hp : L.Perm L') {u w : Node}
    (h : epaxos.ReachIn E L u w) : epaxos.ReachIn E L' u w := by
  induction h with
  | refl => exact .refl _
  | step hxy hy _ ih => exact .step hxy (hp.mem_iff.1 hy) ih

/-- **The bridge**: a valid executed sequence (`chainOk`, what the executor maintains) is a run of
the protocol's executor model, to which its agreement theorem (`epaxos.gryff_runs_agree`) applies. -/
theorem chainOk_runs {C : GMap Node InstAttrs} {Y : List Node} (h : chainOk C Y) :
    epaxos.Runs (fun x => (C.lookup x).isSome) (epaxos.gdep (depsOf C))
      (epaxos.gkeyLt (seqOf C)) [] Y := by
  induction h with
  | nil => exact .nil _
  | snoc X Ls hX hb ih =>
    have hXc := chainOk_closed hX
    obtain ⟨L, hs, hp, hsort, hcm⟩ := hb
    refine epaxos.runs_snoc ih ?_
    rw [List.nil_append, ← depE_eq_gdep]
    obtain ⟨hne, hnd, hnX, hcl, hre⟩ := hs
    refine ⟨?_, fun x hx => ⟨hcm x hx, hnX x (hp.mem_iff.1 hx)⟩, ?_, ?_, ?_⟩
    · intro e; subst e; exact hne (List.Perm.nil_eq hp).symm
    · intro x hx y hy
      rcases hcl x (hp.mem_iff.1 hx) y hy with h1 | h1
      · exact .inl h1
      · exact .inr (hp.mem_iff.2 h1)
    · intro x hx y hy
      exact reachIn_perm hp.symm (reachIn_of_scc ⟨hne, hnd, hnX, hcl, hre⟩ hXc
        (hre x (hp.mem_iff.1 hx) y (hp.mem_iff.1 hy)) (hp.mem_iff.1 hx) (hp.mem_iff.1 hy))
    · exact hsort.imp (fun {a b} hab => (keyLt_eq_gkeyLt C a b).1 hab)

/-! ## The executor's pop step (glue for `strongconnect`'s component execution) -/

/-- `sort.Sort`'s guarantee (no element less than an earlier one) gives `sortedBy` on distinct
instances (the key contains the instance). -/
theorem sortedBy_of_sort (C : GMap Node InstAttrs) (Ls : List Node) (hnd : Ls.Nodup)
    (h : ∀ (i j : Nat) (a b : Node), Ls[i]? = some a → Ls[j]? = some b → i < j →
      ¬ keyLt (keyOf C b) (keyOf C a)) :
    sortedBy C Ls := by
  unfold sortedBy
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hne : Ls[i] ≠ Ls[j] := (List.pairwise_iff_getElem.1 hnd) i j hi hj hij
  have hn := h i j Ls[i] Ls[j] (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
  simp only [keyLt, keyOf] at hn ⊢
  have : Ls[i].1 ≠ Ls[j].1 ∨ Ls[i].2 ≠ Ls[j].2 := by
    by_cases h1 : Ls[i].1 = Ls[j].1
    · exact .inr (fun h2 => hne (Prod.ext h1 h2))
    · exact .inl h1
  omega

/-- Popping `v`'s component `v :: T`, executed in the sorted order `Ls`: the batch is valid after
the executed instances, the executed sequence stays whole components, and each instance of `Ls`
extends a valid sequence when it is executed (the premise of the chain step, `exec_step`). -/
theorem pop_chain {C : GMap Node InstAttrs} {X T Ls : List Node} {v : Node}
    (hs : sccStep (depE C) X (v :: T)) (hcm : ∀ u ∈ v :: T, (C.lookup u).isSome)
    (hch : chainOk C X) (hperm : Ls.Perm (v :: T)) (hsort : sortedBy C Ls) :
    batchOk C X Ls ∧ chainOk C (X ++ Ls) ∧
      ∀ (j : Nat) (n : Node), Ls[j]? = some n → idsOk C (X ++ Ls.take j ++ [n]) := by
  have hb : batchOk C X Ls := ⟨v :: T, hs, hperm, hsort, fun u hu => hcm u (hperm.mem_iff.1 hu)⟩
  exact ⟨hb, .snoc X Ls hch hb, fun j n hj => idsOk_step hch hb j n hj⟩

end Perennial.gryff.replica
