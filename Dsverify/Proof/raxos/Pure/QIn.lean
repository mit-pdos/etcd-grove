/-
The kit's inputs as remote sees them (notes/dsv-quepaxa.md, the kit's design point, option A): the
inputs the kit makes, `QIn := {i : KIn // inputOk i}` (keys of `keyLen` bytes, a put's value
nonempty and not `"nil"`: `kit.go`'s `result` reads a get's value after the key, so the kit is only
correct on these; and short), and the store's specification on them, `qB` (`kvB` through the subtype).

The kit's porcupine model is `pSeq kvB`'s state sets (`ModelSet.lean`, over `KIn`); remote's pending
library takes the model over remote's input type, `QIn`. This file transfers the one to the other,
for any pending-writes store `B` and any predicate `p` on its inputs: a set `S` of `B`'s
configurations whose pending inputs all satisfy `p` (`AllP p S`) stands for the set `pre S` of the
subtype's configurations that map into it; `pSeq (subB B p)`'s step on `pre S` is `pSeq B`'s step
on `S`, mapped by `pre` (`pSeq_sub_step`), and the next set again has its pending inputs in `p`
(`AllP_step`).
-/
module

public import Dsverify.Proof.raxos.Pure.ModelSet

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.raxos.pure

open EtcdGrove.linkv

/-! ## A pending-writes store on a subtype of its inputs -/

section sub
variable {St I O : Type} [DecidableEq I]

/-- `B` on the inputs that satisfy `p`. -/
def subB (B : PendSpec St I O) (p : I → Prop) : PendSpec St {i // p i} O where
  init := B.init
  step i st := B.step i.1 st
  isWrite i := B.isWrite i.1
  isObs i := B.isObs i.1
  obsOk i := B.obsOk i.1

variable {B : PendSpec St I O} {p : I → Prop}

/-- A configuration of the subtype as `B`'s. -/
def cmap (c : PCfg St {i // p i}) : PCfg St I := ⟨c.st, c.pend.map Subtype.val⟩

/-- The configurations of the subtype that map into `S`. -/
def pre (S : PSet St I) : PSet St {i // p i} := fun c => S (cmap c)

/-- Every pending input of every configuration of `S` satisfies `p`. -/
def AllP (p : I → Prop) (S : PSet St I) : Prop := ∀ c, S c → ∀ j ∈ c.pend, p j

theorem cmap_inj {c c' : PCfg St {i // p i}} (h : cmap c = cmap c') : c = c' := by
  obtain ⟨s, l⟩ := c
  obtain ⟨s', l'⟩ := c'
  simp only [cmap, PCfg.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  rw [List.map_inj_right (fun a b h => Subtype.ext h)] at h
  subst h
  rfl

/-- The lift of a list of inputs that all satisfy `p`. -/
def liftL (l : List I) (h : ∀ j ∈ l, p j) : List {i // p i} := l.pmap Subtype.mk h

theorem liftL_map (l : List I) (h : ∀ j ∈ l, p j) : (liftL l h).map Subtype.val = l := by
  unfold liftL
  rw [List.map_pmap]
  simp

theorem map_erase_sub (l : List {i // p i}) (i : {i // p i}) :
    (@List.erase _ instBEqOfDecidableEq l i).map Subtype.val = (l.map Subtype.val).erase i.1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a = i
    · subst h; simp [List.erase_cons]
    · have h' : a.1 ≠ i.1 := fun e => h (Subtype.ext e)
      simp only [List.erase_cons, List.map_cons, beq_iff_eq, h, h', if_false]
      rw [← ih]

theorem perm_of_map_sub {l₁ l₂ : List {i // p i}}
    (h : (l₁.map Subtype.val).Perm (l₂.map Subtype.val)) : l₁.Perm l₂ := by
  rw [List.perm_iff_count] at h ⊢
  intro a
  have := h a.1
  simp only [List.count, List.countP_map] at this
  simp only [List.count]
  have e : ∀ l : List {i // p i}, List.countP (fun x => x == a) l =
      List.countP ((fun x => x == a.1) ∘ Subtype.val) l := by
    intro l
    apply List.countP_congr
    intro x _
    simp [Subtype.ext_iff]
  rw [e, e]
  exact this

theorem silent_map {c c' : PCfg St {i // p i}} (h : PSilent (subB B p) c c') :
    PSilent B (cmap c) (cmap c') := by
  cases h with
  | apply i hm =>
    have := PSilent.apply (P := B) (cmap c) i.1 (List.mem_map_of_mem hm)
    simp only [cmap, subB] at this ⊢
    rw [map_erase_sub]
    exact this
  | perm l hl =>
    exact PSilent.perm (P := B) (cmap c) _ (hl.map _)

theorem reach_map {c c' : PCfg St {i // p i}} (h : PReach (subB B p) c c') :
    PReach B (cmap c) (cmap c') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (silent_map hs) ih

theorem pstep_map {c c' : PCfg St {i // p i}} {i : {i // p i}} {a : Ans O}
    (h : PStep (subB B p) c i a c') : PStep B (cmap c) i.1 a (cmap c') := by
  cases h with
  | ok ho => exact PStep.ok (P := B) (cmap c) i.1 ho
  | errW hw ho => exact PStep.errW (P := B) (cmap c) i.1 hw ho
  | errR hw ho => exact PStep.errR (P := B) (cmap c) i.1 hw ho
  | obs o hob ho => exact PStep.obs (P := B) (cmap c) i.1 o hob ho

theorem silent_lift {c : PCfg St {i // p i}} {d : PCfg St I} (h : PSilent B (cmap c) d) :
    ∃ c', d = cmap c' ∧ PSilent (subB B p) c c' := by
  generalize hc : cmap c = c₀ at h
  cases h with
  | apply j hm =>
    subst hc
    obtain ⟨ĵ, hĵ, rfl⟩ := List.mem_map.1 hm
    exact ⟨⟨(B.step ĵ.1 c.st).1, @List.erase _ instBEqOfDecidableEq c.pend ĵ⟩,
      by simp only [cmap]; rw [map_erase_sub], PSilent.apply (P := subB B p) c ĵ hĵ⟩
  | perm l hl =>
    subst hc
    have hp : ∀ j ∈ l, p j := by
      intro j hj
      obtain ⟨ĵ, -, rfl⟩ := List.mem_map.1 (hl.subset hj)
      exact ĵ.2
    refine ⟨⟨c.st, liftL l hp⟩, by simp only [cmap]; rw [liftL_map], PSilent.perm (P := subB B p) c _ ?_⟩
    have h2 : ((liftL l hp).map Subtype.val).Perm (c.pend.map Subtype.val) := by
      rw [liftL_map]; exact hl
    exact perm_of_map_sub h2

theorem reach_lift {c : PCfg St {i // p i}} {d : PCfg St I} (h : PReach B (cmap c) d) :
    ∃ c', d = cmap c' ∧ PReach (subB B p) c c' := by
  generalize hc : cmap c = c₀ at h
  induction h generalizing c with
  | refl => exact ⟨c, hc.symm, .refl _⟩
  | step hs _ ih =>
    subst hc
    obtain ⟨c₁, rfl, h1⟩ := silent_lift hs
    obtain ⟨c₂, rfl, h2⟩ := ih rfl
    exact ⟨c₂, rfl, .step h1 h2⟩

theorem pstep_lift {c : PCfg St {i // p i}} {i : {i // p i}} {a : Ans O} {d : PCfg St I}
    (h : PStep B (cmap c) i.1 a d) : ∃ c', d = cmap c' ∧ PStep (subB B p) c i a c' := by
  generalize hc : cmap c = c₀ at h
  generalize hi : i.1 = i₀ at h
  cases h with
  | ok ho =>
    subst hc hi
    exact ⟨⟨(B.step i.1 c.st).1, c.pend⟩, rfl, PStep.ok (P := subB B p) c i ho⟩
  | errW hw ho =>
    subst hc hi
    exact ⟨⟨c.st, i :: c.pend⟩, rfl, PStep.errW (P := subB B p) c i hw ho⟩
  | errR hw ho =>
    subst hc hi
    exact ⟨c, rfl, PStep.errR (P := subB B p) c i hw ho⟩
  | obs o hob ho =>
    subst hc hi
    exact ⟨c, rfl, PStep.obs (P := subB B p) c i o hob ho⟩

/-- A configuration of `S` (whose pending inputs satisfy `p`) as the subtype's. -/
theorem cfg_lift {S : PSet St I} (hS : AllP p S) {c : PCfg St I} (hc : S c) :
    ∃ ĉ : PCfg St {i // p i}, c = cmap ĉ :=
  ⟨⟨c.st, liftL c.pend (hS c hc)⟩, by simp only [cmap]; rw [liftL_map]⟩

/-- **`ppost` on the subtype is `ppost` on `B`, mapped**. -/
theorem ppost_sub {S : PSet St I} (hS : AllP p S) (i : {i // p i}) (a : Ans O) :
    ppost (subB B p) (pre S) i a = pre (ppost B S i.1 a) := by
  funext c'
  apply propext
  constructor
  · rintro ⟨c₀, c, c₁, h0, h1, h2, h3⟩
    exact ⟨cmap c₀, cmap c, cmap c₁, h0, reach_map h1, pstep_map h2, reach_map h3⟩
  · rintro ⟨d₀, d, d₁, h0, h1, h2, h3⟩
    obtain ⟨c₀, rfl⟩ := cfg_lift hS h0
    obtain ⟨c, rfl, h1'⟩ := reach_lift h1
    obtain ⟨c₁, rfl, h2'⟩ := pstep_lift h2
    obtain ⟨c₂, hc₂, h3'⟩ := reach_lift h3
    have := cmap_inj hc₂
    subst this
    exact ⟨c₀, c, c₁, h0, h1', h2', h3'⟩

/-- **The configurations after a step from `S` again have their pending inputs in `p`.** -/
theorem AllP_ppost {S : PSet St I} (hS : AllP p S) (i : {i // p i}) (a : Ans O) :
    AllP p (ppost B S i.1 a) := by
  rintro d ⟨d₀, e, e₁, h0, h1, h2, h3⟩
  obtain ⟨c₀, rfl⟩ := cfg_lift hS h0
  obtain ⟨c, rfl, -⟩ := reach_lift (p := p) h1
  obtain ⟨c₁, rfl, -⟩ := pstep_lift (p := p) (i := i) h2
  obtain ⟨c₂, rfl, -⟩ := reach_lift (p := p) h3
  intro j hj
  obtain ⟨ĵ, -, rfl⟩ := List.mem_map.1 hj
  exact ĵ.2

/-- **`pSeq` on the subtype is `pSeq B`, mapped.** -/
theorem pSeq_sub_step {S : PSet St I} (hS : AllP p S) (i : {i // p i}) (a : Ans O) :
    (pSeq (subB B p)).step (pre S) (i, a) = ((pSeq B).step S (i.1, a)).map pre := by
  simp only [pSeq, ppost_sub hS]
  by_cases h : ∃ c, ppost B S i.1 a c
  · rw [if_pos h, if_pos]
    · rfl
    · obtain ⟨c, hc⟩ := h
      obtain ⟨ĉ, rfl⟩ := cfg_lift (AllP_ppost hS i a) hc
      exact ⟨ĉ, (congrFun (ppost_sub hS i a) ĉ).symm ▸ hc⟩
  · rw [if_neg h, if_neg]
    · rfl
    · rintro ⟨ĉ, hc⟩
      exact h ⟨_, (congrFun (ppost_sub hS i a) ĉ) ▸ hc⟩

theorem AllP_step {S T : PSet St I} (hS : AllP p S) (i : {i // p i}) (a : Ans O)
    (h : (pSeq B).step S (i.1, a) = some T) : AllP p T := by
  simp only [pSeq] at h
  split at h
  · cases h; exact AllP_ppost hS i a
  · cases h

theorem pInit_sub : pInit (subB B p) = pre (pInit B) := by
  funext c
  apply propext
  simp only [pInit, pre, cmap, subB]
  constructor
  · rintro rfl; rfl
  · intro h
    obtain ⟨s, l⟩ := c
    simp only [PCfg.mk.injEq, List.map_eq_nil_iff] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

theorem AllP_pInit : AllP p (pInit B) := by
  rintro c rfl j hj
  cases hj

end sub

/-! ## The kit's inputs -/

/-- The inputs the kit makes (`Gen`): `inputOk` (keys of `keyLen` bytes, a put's value nonempty and
not `"nil"`), and short (remote's frames and QuePaxa's messages carry them). -/
def qInOk (i : KIn) : Prop := inputOk i ∧ (i.k.length + i.v.length : Int) < 2 ^ 48

/-- **The kit's inputs** (remote's input type). -/
abbrev QIn := {i : KIn // qInOk i}

/-- **The store's specification on the kit's inputs**: `kvB` on `QIn`. -/
abbrev qB : PendSpec Store QIn KOut := subB kvB qInOk

theorem qB_step (i : QIn) (st : Store) : qB.step i st = kvB.step i.1 st := rfl

theorem qB_isWrite (i : QIn) : qB.isWrite i = i.1.put := rfl

end Perennial.raxos.pure
