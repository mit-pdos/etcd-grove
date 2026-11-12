/-
Lean-first (no Rocq counterpart).

# The list `makeLinkedEntries` builds (2026-10-14)

`linked loc val p l`: the nodes of the entries `l` linked in order, the first one's `prev`
being `p` (`nil` as `makeLinkedEntries` returns it; the head once `checkSingle` inserts it).
`linked_nodesOwn`: with the head before it, it is the list with nothing lifted (`nodesOwn` at
`[]`). `valOf h e` is what the node of `e` holds: its operation's input (a call) or output (a
return), as `makeEntries` puts in the entries (`EntriesFor`).
-/
module

public import Proof.github_com.anishathalye.porcupine.Nodes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

namespace github_com.anishathalye.porcupine

open Theory

section defs
variable [GooseExts]

/-- What the node of entry `e` holds: its operation's input (a call) or output (a return). -/
def valOf (h : List (Op OpV)) (e : Entry) : GoInterface :=
  match h[e.id]? with
  | some o => if e.isRet then o.val.2 else o.val.1
  | none => interface.nil

/-- The first node of `l`, `nil` if `l` is empty. -/
def headLoc (loc : Entry → Loc) : List Entry → Loc
  | [] => null
  | e :: _ => loc e

/-- The node of entry `e`, with previous `p` and next `n`. -/
def linkedNode (loc : Entry → Loc) (val : Entry → GoInterface) (p : Loc) (e : Entry) (n : Loc) :
    node :=
  ⟨val e, if e.isRet then null else loc ⟨true, e.id⟩, W64 e.id, n, p⟩

theorem linkedNode_prev (loc : Entry → Loc) (val : Entry → GoInterface) (p p' : Loc) (e : Entry)
    (n : Loc) : ({ linkedNode loc val p e n with prev' := p' } : node) = linkedNode loc val p' e n :=
  rfl

@[simp] theorem linkedNode_prev' (loc : Entry → Loc) (val : Entry → GoInterface) (p : Loc)
    (e : Entry) (n : Loc) : (linkedNode loc val p e n).prev' = p := rfl

/-- An entry's operation's return is in `l` if its call is. -/
def RetClosed (l : List Entry) : Prop := ∀ y, (⟨false, y⟩ : Entry) ∈ l → (⟨true, y⟩ : Entry) ∈ l

theorem rem_nil (es : List Entry) : rem es [] = es := by
  simp [rem]

/-- The entries of a history are all different: every operation's call and return, `2n` of them
in a list of length `2n`. -/
theorem entriesOk_nodup {α : Type} {h : List (Op α)} {es : List Entry} (hes : EntriesOk h es)
    (hlen : es.length = 2 * h.length) : es.Nodup := by
  let f : Nat → Entry := fun j => ⟨decide (j % 2 = 1), j / 2⟩
  have hL : ((List.range (2 * h.length)).map f).Nodup := by
    apply List.Pairwise.map f _ List.nodup_range
    intro a b hab hf
    simp only [f, Entry.mk.injEq] at hf
    apply hab
    have h1 := hf.2
    have h2 : a % 2 = b % 2 := by
      by_cases ha : a % 2 = 1 <;> by_cases hb : b % 2 = 1 <;> simp_all <;> omega
    omega
  have hsub : (List.range (2 * h.length)).map f ⊆ es := by
    intro e he
    simp only [List.mem_map, List.mem_range] at he
    obtain ⟨j, hj, rfl⟩ := he
    exact (hes.2.1 _).mpr (by simp only [f]; omega)
  have hperm := (List.subperm_of_subset hL hsub).perm_of_length_le (by simp [hlen])
  exact hperm.nodup_iff.mp hL

/-- In a suffix of the entries, a call's return is there too (it is after the call). -/
theorem entriesOk_retClosed_drop {α : Type} {h : List (Op α)} {es : List Entry}
    (hes : EntriesOk h es) (k : Nat) : RetClosed (es.drop k) := by
  intro y hy
  obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hy
  rw [List.getElem_drop] at hje
  have hp : (rem es [])[k + j]? = some ⟨false, y⟩ := by
    rw [rem_nil, List.getElem?_eq_getElem (by simp at hj; omega), hje]
  obtain ⟨q, hq, hqe⟩ := rem_call_has_ret hes hp
  rw [rem_nil] at hqe
  have : (es.drop k)[q - k]? = some ⟨true, y⟩ := by
    rw [List.getElem?_drop, show k + (q - k) = q by omega]; exact hqe
  exact List.mem_of_getElem? this

end defs

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- The nodes of `l` linked in order, the first one's `prev` being `p`. -/
def linked (loc : Entry → Loc) (val : Entry → GoInterface) : Loc → List Entry → IProp GF
  | _, [] => iprop(True)
  | p, e :: l => iprop(loc e ↦ linkedNode loc val p e (headLoc loc l) ∗ linked loc val (loc e) l)

theorem linked_congr {loc loc' : Entry → Loc} {val : Entry → GoInterface} :
    ∀ {l : List Entry} (p : Loc), (∀ e ∈ l, loc' e = loc e) →
      (∀ y, (⟨false, y⟩ : Entry) ∈ l → loc' ⟨true, y⟩ = loc ⟨true, y⟩) →
      linked (GF := GF) loc' val p l = linked loc val p l
  | [], _, _, _ => rfl
  | e :: l, p, h1, h2 => by
    have hl : ∀ e' ∈ l, loc' e' = loc e' := fun e' he' => h1 e' (List.mem_cons_of_mem _ he')
    have hhead : headLoc loc' l = headLoc loc l := by
      cases l with
      | nil => rfl
      | cons a l => exact h1 a (by simp)
    have hnode : linkedNode loc' val p e (headLoc loc' l) = linkedNode loc val p e (headLoc loc l) := by
      unfold linkedNode
      rw [hhead]
      obtain ⟨b, y⟩ := e
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [h2 y (by simp)]
      · rfl
    simp only [linked]
    rw [hnode, h1 e (by simp),
      linked_congr (loc e) hl (fun y hy => h2 y (List.mem_cons_of_mem _ hy))]

/-- `makeLinkedEntries`'s step: the node `n` of `a`, inserted before the list `l` (whose first
`prev` is now `n`), is the list `a :: l` (with `a`'s node at `n`). -/
theorem linked_prepend (loc : Entry → Loc) (val : Entry → GoInterface) (a : Entry) (n : Loc)
    (l : List Entry) (hal : a ∉ l) (hrc : RetClosed l) :
    n ↦ linkedNode (upd loc a n) val null a (headLoc loc l) ∗ linked (GF := GF) loc val n l ⊢
      linked (upd loc a n) val null (a :: l) := by
  have h1 : ∀ e ∈ l, upd loc a n e = loc e := fun e he => upd_ne (fun h => hal (h ▸ he))
  have h2 : ∀ y, (⟨false, y⟩ : Entry) ∈ l → upd loc a n ⟨true, y⟩ = loc ⟨true, y⟩ :=
    fun y hy => h1 _ (hrc y hy)
  have hhead : headLoc (upd loc a n) l = headLoc loc l := by
    cases l with
    | nil => rfl
    | cons b l => exact h1 b (by simp)
  simp only [linked]
  rw [upd_self, hhead, linked_congr n h1 h2]

/-- The nodes of `l` after the slot `p`, as slots of a list `p :: l.map some`. -/
theorem linked_nb (hd : Loc) (loc : Entry → Loc) (val : Entry → GoInterface) :
    ∀ (l : List Entry) (p : Slot), l.Nodup → p ∉ l.map some →
      linked (GF := GF) loc val (slotLoc hd loc p) l ⊢
        [∗list] e ∈ l, loc e ↦ nodeVal hd loc val (some e) (nb (p :: l.map some) (some e))
  | [], _, _, _ => by iintro -; exact BigSepL.bigSepL_nil.2
  | a :: l, p, hnd, hp => by
    simp only [linked]
    rw [List.nodup_cons] at hnd
    have hal : (some a : Slot) ∉ l.map some := by simpa using hnd.1
    iintro ⟨Ha, Hl⟩
    have h := linked_nb hd loc val l (some a) hnd.2 hal
    simp only [slotLoc] at h
    ihave Hl := h $$ Hl
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ha]
    · have hnb : nb (p :: (a :: l).map some) (some a) = (some p, (l.map some).head?) := by
        have hpa : p ≠ some a := fun h => hp (by simp [h])
        simp only [nb, List.map_cons, prevOf, nextOf, List.head?_cons, ↓reduceIte, hpa]
      rw [hnb]
      have : linkedNode loc val (slotLoc hd loc p) a (headLoc loc l) =
          nodeVal hd loc val (some a) (some p, (l.map some).head?) := by
        cases l <;> rfl
      rw [this]
      iexact Ha
    · iapply BigSepL.bigSepL_mono ?_ $$ Hl
      intro k e hk
      have he : e ∈ l := List.mem_of_getElem? hk
      have hpe : p ≠ some e := fun h => hp (by simp [h, he])
      have hae : a ≠ e := fun h => hnd.1 (h ▸ he)
      have hnb : nb (p :: (a :: l).map some) (some e) = nb (some a :: l.map some) (some e) := by
        simp only [nb, List.map_cons, prevOf, nextOf, List.head?_cons, Option.some.injEq, hae,
          ↓reduceIte, hpe]
      rw [hnb]

/-- The head and the nodes linked after it: the list with nothing lifted. -/
theorem linked_nodesOwn (hd : Loc) (loc : Entry → Loc) (val : Entry → GoInterface)
    (es : List Entry) (hnd : es.Nodup) (hnn : hd ≠ null ∧ ∀ e ∈ es, loc e ≠ null) :
    hd ↦ (⟨interface.nil, null, W64 (-1), headLoc loc es, null⟩ : node) ∗
      linked (GF := GF) loc val hd es ⊢ nodesOwn hd loc val es [] := by
  iintro ⟨Hhd, Hl⟩
  unfold nodesOwn nodesG
  have h := linked_nb (GF := GF) hd loc val es none hnd (by simp)
  simp only [slotLoc] at h
  ihave Hl := h $$ Hl
  isplitl
  · have hcur : cur es [] = none :: es.map some := by simp [cur, rem_nil]
    simp only [slots, layout, hcur]
    iapply BigSepL.bigSepL_cons.2
    simp only [slotLoc]
    isplitl [Hhd]
    · have : nb (none :: es.map some) none = (none, (es.map some).head?) := by
        have : prevOf (es.map some) none = none := prevOf_not_mem (by simp)
        simp [nb, prevOf, nextOf, this]
      rw [this]
      have : (⟨interface.nil, null, W64 (-1), headLoc loc es, null⟩ : node) =
          nodeVal hd loc val none (none, (es.map some).head?) := by
        cases es <;> rfl
      rw [← this]
      iexact Hhd
    · rw [BigSepL.bigSepL_map]
      iexact Hl
  · ipureintro; exact hnn

end heap

end github_com.anishathalye.porcupine

end Perennial
