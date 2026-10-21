/-
Lean-first (no Rocq counterpart).

# The search's linked list, in the heap (2026-10-14)

The nodes of the list (`node`, checker.go) behind its head `hd`: the node of entry `e` is at
`loc e`, its `value` is `val e` (the operation's input for a call, its output for a return),
its `match` the node of its return for a call and `nil` for a return, its `id` the operation's;
the head has a `nil` value and match and id `-1`. Each slot's `prev` and `next` are given by a
function `G` (`nodesG`); `nodesOwn` is the list when the operations `B` are lifted (`G` is
`layout es B`, `Layout.lean`). `nodesG_acc` takes one node out (and puts it back with new
neighbours), which is how `lift`, `unlift` and `checkSingle` read and write fields.
-/
module

public import Proof.github_com.anishathalye.porcupine.Layout
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

namespace github_com.anishathalye.porcupine

open Theory

section defs
variable [ext : FfiSyntax]

/-- Where a slot's node is. -/
def slotLoc (hd : Loc) (loc : Entry → Loc) : Slot → Loc
  | none => hd
  | some e => loc e

/-- A `prev` or `next` field: `nil`, or a slot's node. -/
def nbrLoc (hd : Loc) (loc : Entry → Loc) : Option Slot → Loc
  | none => null
  | some x => slotLoc hd loc x

/-- The node of slot `x` with neighbours `pn` (previous, next). -/
def nodeVal (hd : Loc) (loc : Entry → Loc) (val : Entry → GoInterface) (x : Slot)
    (pn : Option Slot × Option Slot) : node :=
  match x with
  | none => ⟨interface.nil, null, W64 (-1), nbrLoc hd loc pn.2, nbrLoc hd loc pn.1⟩
  | some e => ⟨val e, if e.isRet then null else loc ⟨true, e.id⟩, W64 e.id,
      nbrLoc hd loc pn.2, nbrLoc hd loc pn.1⟩

theorem nodeVal_next (hd : Loc) (loc : Entry → Loc) (val : Entry → GoInterface) (x : Slot)
    (pn : Option Slot × Option Slot) (n : Option Slot) :
    ({ nodeVal hd loc val x pn with next' := nbrLoc hd loc n } : node) =
      nodeVal hd loc val x (pn.1, n) := by
  cases x <;> rfl

theorem nodeVal_next_some (hd : Loc) (loc : Entry → Loc) (val : Entry → GoInterface) (x : Slot)
    (pn : Option Slot × Option Slot) (n : Slot) :
    ({ nodeVal hd loc val x pn with next' := slotLoc hd loc n } : node) =
      nodeVal hd loc val x (pn.1, some n) := by
  cases x <;> rfl

theorem nodeVal_prev_some (hd : Loc) (loc : Entry → Loc) (val : Entry → GoInterface) (x : Slot)
    (pn : Option Slot × Option Slot) (p : Slot) :
    ({ nodeVal hd loc val x pn with prev' := slotLoc hd loc p } : node) =
      nodeVal hd loc val x (some p, pn.2) := by
  cases x <;> rfl

@[simp] theorem nodeVal_next' (hd : Loc) (loc : Entry → Loc) (val : Entry → GoInterface)
    (x : Slot) (pn : Option Slot × Option Slot) :
    (nodeVal hd loc val x pn).next' = nbrLoc hd loc pn.2 := by
  cases x <;> rfl

@[simp] theorem nodeVal_prev' (hd : Loc) (loc : Entry → Loc) (val : Entry → GoInterface)
    (x : Slot) (pn : Option Slot × Option Slot) :
    (nodeVal hd loc val x pn).prev' = nbrLoc hd loc pn.1 := by
  cases x <;> rfl

@[simp] theorem nodeVal_match_some (hd : Loc) (loc : Entry → Loc) (val : Entry → GoInterface)
    (e : Entry) (pn : Option Slot × Option Slot) :
    (nodeVal hd loc val (some e) pn).match' = if e.isRet then null else loc ⟨true, e.id⟩ := rfl

@[simp] theorem nodeVal_value_some (hd : Loc) (loc : Entry → Loc) (val : Entry → GoInterface)
    (e : Entry) (pn : Option Slot × Option Slot) :
    (nodeVal hd loc val (some e) pn).value' = val e := rfl

@[simp] theorem nodeVal_id_some (hd : Loc) (loc : Entry → Loc) (val : Entry → GoInterface)
    (e : Entry) (pn : Option Slot × Option Slot) :
    (nodeVal hd loc val (some e) pn).id' = W64 e.id := rfl

/-- All slots: the head and every entry's node. -/
def slots (es : List Entry) : List Slot := none :: es.map some

theorem slots_nodup {es : List Entry} (hnd : es.Nodup) : (slots es).Nodup := by
  unfold slots; rw [List.nodup_cons]; exact ⟨by simp, nodup_map_some hnd⟩

theorem mem_slots_some {es : List Entry} {e : Entry} (he : e ∈ es) : some e ∈ slots es := by
  simp [slots, he]

theorem mem_slots_none {es : List Entry} : none ∈ slots es := by simp [slots]

theorem cur_sub_slots {es : List Entry} {B : List Nat} {x : Slot} (hx : x ∈ cur es B) :
    x ∈ slots es := by
  unfold cur at hx; unfold slots
  simp only [List.mem_cons, List.mem_map] at hx ⊢
  rcases hx with rfl | ⟨e, he, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨e, (List.mem_filter.mp he).1, rfl⟩

theorem slotLoc_ne_null {hd : Loc} {loc : Entry → Loc} {es : List Entry}
    (hnn : hd ≠ null ∧ ∀ e ∈ es, loc e ≠ null) {x : Slot} (hx : x ∈ slots es) :
    slotLoc hd loc x ≠ null := by
  cases x with
  | none => exact hnn.1
  | some e =>
    simp only [slots, List.mem_cons, reduceCtorEq, List.mem_map, Option.some.injEq,
      false_or] at hx
    obtain ⟨e', he', rfl⟩ := hx
    exact hnn.2 e' he'

end defs

section heap
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- Every slot's node, with neighbours `G`. -/
def nodesG (hd : Loc) (loc : Entry → Loc) (val : Entry → GoInterface) (es : List Entry)
    (G : Slot → Option Slot × Option Slot) : IProp GF :=
  iprop([∗list] x ∈ slots es, slotLoc hd loc x ↦ nodeVal hd loc val x (G x))

/-- The list when the operations `B` are lifted. -/
def nodesOwn (hd : Loc) (loc : Entry → Loc) (val : Entry → GoInterface) (es : List Entry)
    (B : List Nat) : IProp GF :=
  iprop(nodesG hd loc val es (layout es B) ∗ ⌜hd ≠ null ∧ ∀ e ∈ es, loc e ≠ null⌝)

theorem bigSepL_upd_acc {A V : Type} [DecidableEq A] {Φ : A → V → IProp GF} {l : List A}
    (hnd : l.Nodup) {x : A} (hx : x ∈ l) (F : A → V) :
    ([∗list] y ∈ l, Φ y (F y)) ⊢ Φ x (F x) ∗ ∀ v, Φ x v -∗ [∗list] y ∈ l, Φ y (upd F x v y) := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    show ((Φ a (F a) ∗ [∗list] y ∈ l, Φ y (F y)) ⊢ Φ x (F x) ∗ ∀ v, Φ x v -∗ Φ a (upd F x v a) ∗ [∗list] y ∈ l, Φ y (upd F x v y))
    by_cases hax : a = x
    · subst hax
      iintro ⟨Ha, Hl⟩
      iframe Ha
      iintro %v Hv
      simp only [upd_self]
      iframe Hv
      iapply BigSepL.bigSepL_mono (Φ := fun _ y => Φ y (F y)) ?_ $$ Hl
      intro k y hk
      have hy : y ∈ l := List.mem_of_getElem? hk
      have hya : y ≠ a := fun h => hnd.1 (h ▸ hy)
      rw [upd_ne hya]
    · have hx' : x ∈ l := (List.mem_cons.mp hx).resolve_left (Ne.symm hax)
      iintro ⟨Ha, Hl⟩
      icases ih hnd.2 hx' $$ Hl with ⟨Hx, Hback⟩
      iframe Hx
      iintro %v Hv
      rw [upd_ne hax]
      iframe Ha
      iapply Hback $$ Hv

/-- Take the node of slot `x` out, to put it back with new neighbours. -/
theorem nodesG_acc {hd : Loc} {loc : Entry → Loc} {val : Entry → GoInterface} {es : List Entry}
    (hnd : es.Nodup) {x : Slot} (hx : x ∈ slots es) (G : Slot → Option Slot × Option Slot) :
    nodesG (GF := GF) hd loc val es G ⊢ slotLoc hd loc x ↦ nodeVal hd loc val x (G x) ∗
      ∀ pn, slotLoc hd loc x ↦ nodeVal hd loc val x pn -∗ nodesG hd loc val es (upd G x pn) := by
  unfold nodesG
  exact bigSepL_upd_acc (Φ := fun x pn => iprop(slotLoc hd loc x ↦ nodeVal hd loc val x pn))
    (slots_nodup hnd) hx G

/-- Take the node of slot `x` out, to put it back unchanged. -/
theorem nodesG_read {hd : Loc} {loc : Entry → Loc} {val : Entry → GoInterface} {es : List Entry}
    (hnd : es.Nodup) {x : Slot} (hx : x ∈ slots es) (G : Slot → Option Slot × Option Slot) :
    nodesG (GF := GF) hd loc val es G ⊢ slotLoc hd loc x ↦ nodeVal hd loc val x (G x) ∗
      (slotLoc hd loc x ↦ nodeVal hd loc val x (G x) -∗ nodesG hd loc val es G) := by
  iintro H
  icases nodesG_acc hnd hx G $$ H with ⟨Hx, Hback⟩
  iframe Hx
  iintro Hx
  ihave H := Hback $$ %(G x) Hx
  have : upd G x (G x) = G := by funext y; by_cases h : y = x <;> simp [upd, h]
  rw [this]
  iexact H

theorem nodesG_congr {hd : Loc} {loc : Entry → Loc} {val : Entry → GoInterface} {es : List Entry}
    {G G' : Slot → Option Slot × Option Slot} (h : ∀ x ∈ slots es, G x = G' x) :
    nodesG (GF := GF) hd loc val es G = nodesG hd loc val es G' := by
  unfold nodesG
  apply BigSepL.bigSepL_eq
  intro k x hk
  rw [h x (List.mem_of_getElem? hk)]

end heap

end github_com.anishathalye.porcupine

end Perennial
