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

/-! ## A pending-writes store on a subtype of its outputs -/

section out
variable {St I O : Type} [DecidableEq I]

open Classical in
/-- `o` as an output of the subtype `q`, or `d` if it is not one. -/
noncomputable def clampO {q : O → Prop} (d : {o // q o}) (o : O) : {o // q o} := if h : q o then ⟨o, h⟩ else d

theorem clampO_of {q : O → Prop} (d : {o // q o}) {o : O} (h : q o) : clampO d o = ⟨o, h⟩ := by
  unfold clampO; rw [dif_pos h]

/-- `B` with its outputs clamped into the subtype `q` (`d` for any other output): `B` itself on
the states of an invariant `g` whose outputs are all in `q` (`OutInv`). -/
noncomputable def outB (B : PendSpec St I O) (q : O → Prop) (d : {o // q o}) : PendSpec St I {o // q o} where
  init := B.init
  step i st := ((B.step i st).1, clampO d (B.step i st).2)
  isWrite i := B.isWrite i
  isObs i := B.isObs i
  obsOk i st o := B.obsOk i st o.1

/-- A state invariant `g` of `B`, kept by every step, on whose states every output is in `q`. -/
structure OutInv (B : PendSpec St I O) (q : O → Prop) (g : St → Prop) : Prop where
  keep : ∀ i st, g st → g (B.step i st).1
  out : ∀ i st, g st → q (B.step i st).2

/-- Every configuration of `S` has its state in `g`. -/
def AllG (g : St → Prop) (S : PSet St I) : Prop := ∀ c, S c → g c.st

/-- An answer of the subtype as `B`'s. -/
def ansVal {q : O → Prop} : Ans {o // q o} → Ans O
  | .ok o => .ok o.1
  | .err => .err

variable {B : PendSpec St I O} {q : O → Prop} {d : {o // q o}} {g : St → Prop}

theorem silent_out {c c' : PCfg St I} : PSilent (outB B q d) c c' ↔ PSilent B c c' := by
  constructor
  · intro h; cases h with
    | apply i hm => exact PSilent.apply (P := B) c i hm
    | perm l hl => exact PSilent.perm (P := B) c l hl
  · intro h; cases h with
    | apply i hm => exact PSilent.apply (P := outB B q d) c i hm
    | perm l hl => exact PSilent.perm (P := outB B q d) c l hl

theorem reach_out {c c' : PCfg St I} : PReach (outB B q d) c c' ↔ PReach B c c' := by
  constructor
  · intro h; induction h with
    | refl => exact .refl _
    | step hs _ ih => exact .step (silent_out.1 hs) ih
  · intro h; induction h with
    | refl => exact .refl _
    | step hs _ ih => exact .step (silent_out.2 hs) ih

theorem silent_g (hg : OutInv B q g) {c c' : PCfg St I} (h : PSilent B c c') (hc : g c.st) :
    g c'.st := by
  cases h with
  | apply i _ => exact hg.keep i c.st hc
  | perm _ _ => exact hc

theorem reach_g (hg : OutInv B q g) {c c' : PCfg St I} (h : PReach B c c') (hc : g c.st) :
    g c'.st := by
  induction h with
  | refl => exact hc
  | step hs _ ih => exact ih (silent_g hg hs hc)

theorem pstep_out (hg : OutInv B q g) {c c' : PCfg St I} {i : I} {a : Ans {o // q o}}
    (hc : g c.st) : PStep (outB B q d) c i a c' ↔ PStep B c i (ansVal a) c' := by
  constructor
  · intro h; cases h with
    | ok ho =>
      have e : clampO d (B.step i c.st).2 = ⟨(B.step i c.st).2, hg.out i c.st hc⟩ :=
        clampO_of d _
      simp only [outB] at ho ⊢
      rw [e]
      exact PStep.ok (P := B) c i ho
    | errW hw ho => exact PStep.errW (P := B) c i hw ho
    | errR hw ho => exact PStep.errR (P := B) c i hw ho
    | obs o hob ho => exact PStep.obs (P := B) c i o.1 hob ho
  · intro h
    generalize ha : ansVal a = a' at h
    cases h with
    | ok ho =>
      have e : clampO d (B.step i c.st).2 = ⟨(B.step i c.st).2, hg.out i c.st hc⟩ :=
        clampO_of d _
      cases a with
      | err => cases ha
      | ok o =>
        simp only [ansVal, Ans.ok.injEq] at ha
        have : o = ⟨(B.step i c.st).2, hg.out i c.st hc⟩ := Subtype.ext ha
        subst this
        have h := PStep.ok (P := outB B q d) c i ho
        simp only [outB] at h
        rw [e] at h
        exact h
    | errW hw ho =>
      cases a with
      | err => exact PStep.errW (P := outB B q d) c i hw ho
      | ok o => cases ha
    | errR hw ho =>
      cases a with
      | err => exact PStep.errR (P := outB B q d) c i hw ho
      | ok o => cases ha
    | obs o hob ho =>
      cases a with
      | err => cases ha
      | ok o' =>
        simp only [ansVal, Ans.ok.injEq] at ha
        subst ha
        exact PStep.obs (P := outB B q d) c i o' hob ho

theorem pstep_g (hg : OutInv B q g) {c c' : PCfg St I} {i : I} {a : Ans O}
    (h : PStep B c i a c') (hc : g c.st) : g c'.st := by
  cases h with
  | ok _ => exact hg.keep i c.st hc
  | errW _ _ => exact hc
  | errR _ _ => exact hc
  | obs _ _ _ => exact hc

/-- **`ppost` with the outputs clamped is `B`'s**, on states of the invariant. -/
theorem ppost_out (hg : OutInv B q g) {S : PSet St I} (hS : AllG g S) (i : I)
    (a : Ans {o // q o}) : ppost (outB B q d) S i a = ppost B S i (ansVal a) := by
  funext c'
  apply propext
  constructor
  · rintro ⟨c₀, c, c₁, h0, h1, h2, h3⟩
    have h1' := reach_out.1 h1
    exact ⟨c₀, c, c₁, h0, h1', (pstep_out hg (reach_g hg h1' (hS _ h0))).1 h2, reach_out.1 h3⟩
  · rintro ⟨c₀, c, c₁, h0, h1, h2, h3⟩
    exact ⟨c₀, c, c₁, h0, reach_out.2 h1, (pstep_out hg (reach_g hg h1 (hS _ h0))).2 h2,
      reach_out.2 h3⟩

theorem AllG_ppost (hg : OutInv B q g) {S : PSet St I} (hS : AllG g S) (i : I) (a : Ans O) :
    AllG g (ppost B S i a) := by
  rintro c' ⟨c₀, c, c₁, h0, h1, h2, h3⟩
  exact reach_g hg h3 (pstep_g hg h2 (reach_g hg h1 (hS _ h0)))

/-- **`pSeq` with the outputs clamped is `pSeq B`**, on sets of states of the invariant. -/
theorem pSeq_out_step (hg : OutInv B q g) {S : PSet St I} (hS : AllG g S) (i : I)
    (a : Ans {o // q o}) :
    (pSeq (outB B q d)).step S (i, a) = (pSeq B).step S (i, ansVal a) := by
  have e := ppost_out (d := d) hg hS i a
  simp only [pSeq]
  rw [e]

theorem AllG_step (hg : OutInv B q g) {S T : PSet St I} (hS : AllG g S) (i : I) (a : Ans O)
    (h : (pSeq B).step S (i, a) = some T) : AllG g T := by
  simp only [pSeq] at h
  split at h
  · cases h; exact AllG_ppost hg hS i a
  · cases h

theorem pInit_out : pInit (outB B q d) = pInit B := rfl

end out

/-! ## The kit's inputs -/

/-- The inputs the kit makes (`Gen`): `inputOk` (keys of `keyLen` bytes, a put's value nonempty and
not `"nil"`), and short (remote's frames and QuePaxa's messages carry them). -/
def qInOk (i : KIn) : Prop := inputOk i ∧ (i.k.length + i.v.length : Int) < 2 ^ 48

/-- **The kit's inputs** (remote's input type). -/
abbrev QIn := {i : KIn // qInOk i}

/-- The outputs the kit's codec encodes (`EncOut`: two flag bytes and the value, below `2^63`
bytes). -/
def qOutOk (o : KOut) : Prop := (o.v.length : Int) + 2 < 2 ^ 63

/-- **The kit's outputs** (remote's output type: its codec must encode every output injectively
within `2^63` bytes, so the outputs are bounded). -/
abbrev QOut := {o : KOut // qOutOk o}

/-- The empty answer, as a `QOut`. -/
def qOut0 : QOut := ⟨⟨false, []⟩, by unfold qOutOk; simp⟩

/-- A store whose values are short (below `2^48` bytes: the kit's inputs' values). -/
def shortSt (st : Store) : Prop := ∀ k v, st k = some v → (v.length : Int) < 2 ^ 48

/-- **The store's specification on the kit's inputs and outputs**: `kvB` on `QIn`, its outputs
clamped into `QOut` (on short stores, every output is one: `qB_outInv`). -/
noncomputable abbrev qB : PendSpec Store QIn QOut := outB (subB kvB qInOk) qOutOk qOut0

theorem qB_step (i : QIn) (st : Store) :
    qB.step i st = ((kvB.step i.1 st).1, clampO qOut0 (kvB.step i.1 st).2) := rfl

theorem qB_isWrite (i : QIn) : qB.isWrite i = i.1.put := rfl

/-- The initial configurations (on the kit's inputs) have a short store. -/
theorem allG_pInit : AllG shortSt (pre (p := qInOk) (pInit kvB)) := by
  rintro c hc k v hk
  simp only [pre, cmap, pInit, PCfg.mk.injEq] at hc
  rw [hc.1] at hk
  simp [kvB] at hk

/-- Short stores are kept by `kvB`'s steps on the kit's inputs, and their outputs are `QOut`s. -/
theorem qB_outInv : OutInv (subB kvB qInOk) qOutOk shortSt where
  keep i st h := by
    intro k v hk
    simp only [subB, kvB] at hk
    split at hk
    · simp only at hk
      split at hk
      · cases hk; have := i.2.2; omega
      · exact h k v hk
    · exact h k v hk
  out i st h := by
    unfold qOutOk
    simp only [subB, kvB]
    split
    · simp
    · simp only
      split
      · rename_i v hv; have := h _ v hv; simp only; omega
      · simp

end Perennial.raxos.pure
