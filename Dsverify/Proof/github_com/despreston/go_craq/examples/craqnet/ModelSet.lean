/-
The key-value map's porcupine model, pure (notes/dsv-craq.md, P2).

* **The store** `kvB`: linkv's pending-writes store (`linkv.PendSpec`) of the key-value map on
  bounded strings (`Str8`, shorter than 256 bytes: the kit's `Codec` writes a string's length in one
  byte). Its state `St` maps keys to bounded values; its inputs `KIn` are bounded gets and puts
  (`inOk`); a put is a write (one of unknown outcome is pending: it may take effect later, once, or
  never).
* **The Go model's state** `(a, P)` (kit.go's `State{M, Pend}`: the map, the puts pending) does not
  determine the set of configurations the history reached (a pending put may have taken effect
  before a later put of its key overwrote it, or not, depending on the order of the history), so
  the kit's `Equal` is always false and the state only **brackets** the set (`Sim a P S`): it holds
  every configuration reachable from `⟨a, P⟩` (`Funl`) and only configurations reachable from `a`
  with some of `P` pending (`Fall`).
* **The simulation** `sim_step`: from a bracketed set, the model's step on `(i, o)` is defined
  exactly when the Go step (`goStep`, kit.go's `step` on the decoded answer) allows it, and the next
  set is bracketed by the Go step's next state. The lemmas: `reach_cons` (a pending input that never
  fires), `reach_put` (a put commutes past late effects at other keys, and overwrites those at its
  own), `reach_key` (a key's value after late effects: its value before, or a pending put's, which
  can be taken to have fired first).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.PendModel
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Protocol

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

namespace github_com.despreston.go_craq.examples.craqnet

open EtcdGrove EtcdGrove.linkv github_com.despreston.go_craq

/-! ## The store -/

/-- A bounded string: shorter than 256 bytes. -/
abbrev Str8 := {s : GoString // s.length < 256}

/-- The bounded inputs: a get's key, a put's key and value: a key the protocol handles (`keyOk`:
at most 2 bytes; the kit's keys are `"k0"` and `"k1"`), a value a `Str8`. -/
def inOk : KvInput → Prop
  | .get k => keyOk k
  | .put k x => keyOk k ∧ x.length < 256

/-- The store's inputs. -/
abbrev KIn := {i : KvInput // inOk i}

/-- `KIn`'s `BEq` is its decidable equality's (the instance linkv's pending lists erase with). -/
@[reducible] instance (priority := high) KIn.beq : BEq KIn := instBEqOfDecidableEq

/-- The store's outputs: `got v`, a get's value (`none`: not found) or a put's success (`got
none`: kit.go answers both with `Out{}`, so the store has one output for both, and which one it
is depends on the input: `Kit.lean`'s `liftOut`); `bad`, an answer no operation gives (what an
ill-formed `Out` decodes to; the store never outputs it). -/
inductive KOut where
  | got (v : Option Str8)
  | bad
deriving DecidableEq

/-- The store's state: a key's bounded value, if any. -/
abbrev St := GoString → Option Str8

/-- `a` with `k` mapped to `x`. -/
def upd (a : St) (k : GoString) (x : Str8) : St := fun k' => if k' = k then some x else a k'

/-- The step: a get answers its key's value; a put sets it and answers `got none`. -/
def kvStep : KIn → St → St × KOut
  | ⟨.get k, _⟩, a => (a, .got (a k))
  | ⟨.put k x, h⟩, a => (upd a k ⟨x, h.2⟩, .got none)

/-- Whether an input is a put. -/
def isPut (i : KIn) : Bool :=
  match i.1 with
  | .put _ _ => true
  | .get _ => false

/-- **The key-value map with failed puts** (linkv's pending-writes store). -/
def kvB : PendSpec St KIn KOut where
  init := fun _ => none
  step := kvStep
  isWrite := isPut

theorem upd_same (a : St) (k : GoString) (x y : Str8) : upd (upd a k x) k y = upd a k y := by
  funext k'; unfold upd; by_cases h : k' = k <;> simp [h]

theorem upd_comm (a : St) (k k' : GoString) (x y : Str8) (h : k' ≠ k) :
    upd (upd a k x) k' y = upd (upd a k' y) k x := by
  funext j; unfold upd
  by_cases h1 : j = k' <;> by_cases h2 : j = k <;> simp_all

theorem upd_get (a : St) (k : GoString) (x : Str8) : upd a k x k = some x := by
  simp [upd]

theorem upd_ne (a : St) (k k' : GoString) (x : Str8) (h : k' ≠ k) : upd a k x k' = a k' := by
  simp [upd, h]

theorem step_put (k x : GoString) (h : inOk (.put k x)) (a : St) :
    kvB.step ⟨.put k x, h⟩ a = (upd a k ⟨x, h.2⟩, .got none) := rfl

theorem step_get (k : GoString) (h : inOk (.get k)) (a : St) :
    kvB.step ⟨.get k, h⟩ a = (a, .got (a k)) := rfl

/-! ## Late effects -/

/-- A pending input that never fires rides along. -/
theorem reach_cons (i : KIn) {c c' : PCfg St KIn} (h : PReach kvB c c') :
    PReach kvB ⟨c.st, i :: c.pend⟩ ⟨c'.st, i :: c'.pend⟩ := by
  induction h with
  | refl c => exact .refl _
  | @step c c₁ c₂ hs _ ih =>
    refine PReach.trans ?_ ih
    cases hs with
    | apply j hj =>
      refine .step (.apply ⟨c.st, i :: c.pend⟩ j (List.mem_cons_of_mem _ hj)) (.single (.perm _ _ ?_))
      by_cases hij : i = j
      · subst hij
        simp only [List.erase_cons_head]
        exact (List.perm_cons_erase hj).symm
      · rw [List.erase_cons_tail (by simpa using hij)]
    | perm p hp => exact .single (.perm _ _ (hp.cons i))

/-- **A put after late effects**: the same as the put first, then the late effects at other keys
(those at its own key are overwritten: they need not be pending). -/
theorem reach_put (k : GoString) (x : Str8) {c c' : PCfg St KIn} (h : PReach kvB c c') :
    ∃ Q, Q.Subperm c.pend ∧ PReach kvB ⟨upd c.st k x, Q⟩ ⟨upd c'.st k x, c'.pend⟩ := by
  induction h with
  | refl c => exact ⟨c.pend, List.Subperm.refl _, .refl _⟩
  | @step c c₁ c₂ hs _ ih =>
    obtain ⟨Q₁, hQ₁, hr⟩ := ih
    cases hs with
    | apply j hj =>
      obtain ⟨k' | ⟨k', y⟩, hj'⟩ := j
      · exact ⟨Q₁, hQ₁.trans (List.erase_sublist ..).subperm, hr⟩
      · by_cases hk : k' = k
        · subst hk
          refine ⟨Q₁, hQ₁.trans (List.erase_sublist ..).subperm, ?_⟩
          simpa [step_put, upd_same] using hr
        · refine ⟨⟨.put k' y, hj'⟩ :: Q₁, ?_, ?_⟩
          · exact ((List.subperm_cons _).2 hQ₁).trans (List.perm_cons_erase hj).symm.subperm
          · refine .step (.apply ⟨upd c.st k x, _ :: Q₁⟩ _ List.mem_cons_self) ?_
            simp only [step_put, List.erase_cons_head]
            rw [upd_comm _ _ _ _ _ hk]
            simpa [step_put] using hr
    | perm p hp => exact ⟨Q₁, hQ₁.trans hp.subperm, hr⟩

/-- **A key after late effects**: its value before, or the value of a pending put of it, which
may be taken to have fired first (the others at the key before it are overwritten). -/
theorem reach_key (k : GoString) {c c' : PCfg St KIn} (h : PReach kvB c c') :
    c'.st k = c.st k ∨ ∃ (x : Str8) (i : KIn), c'.st k = some x ∧ i.1 = .put k x.1 ∧
      i ∈ c.pend ∧ ∃ Q, Q.Subperm (c.pend.erase i) ∧ PReach kvB ⟨upd c.st k x, Q⟩ c' := by
  induction h with
  | refl c => exact .inl rfl
  | @step c c₁ c₂ hs hr ih =>
    cases hs with
    | apply j hj =>
      obtain ⟨k' | ⟨k', y⟩, hj'⟩ := j
      · -- a get: nothing changes
        rcases ih with h1 | ⟨x, i, hx, hi, him, Q, hQ, hr'⟩
        · exact .inl h1
        · refine .inr ⟨x, i, hx, hi, List.mem_of_mem_erase him, Q, ?_, hr'⟩
          rw [List.erase_comm] at hQ
          exact hQ.trans (List.erase_sublist ..).subperm
      · rcases ih with h1 | ⟨x, i, hx, hi, him, Q, hQ, hr'⟩
        · by_cases hk : k' = k
          · subst hk
            refine .inr ⟨⟨y, hj'.2⟩, ⟨.put k' y, hj'⟩, ?_, rfl, hj, _, List.Subperm.refl _, hr⟩
            simpa [step_put, upd_get] using h1
          · exact .inl (by simpa [step_put, upd_ne _ _ _ _ (Ne.symm hk)] using h1)
        · refine .inr ⟨x, i, hx, hi, List.mem_of_mem_erase him, ?_⟩
          by_cases hk : k' = k
          · subst hk
            refine ⟨Q, ?_, by simpa [step_put, upd_same] using hr'⟩
            rw [List.erase_comm] at hQ
            exact hQ.trans (List.erase_sublist ..).subperm
          · have hji : (⟨.put k' y, hj'⟩ : KIn) ≠ i := by
              intro e; rw [← e] at hi; simp at hi; exact hk hi.1
            refine ⟨⟨.put k' y, hj'⟩ :: Q, ?_, ?_⟩
            · rw [List.erase_comm] at hQ
              exact ((List.subperm_cons _).2 hQ).trans
                (List.perm_cons_erase (List.mem_erase_of_ne hji |>.2 hj)).symm.subperm
            · refine .step (.apply ⟨upd c.st k x, _ :: Q⟩ _ List.mem_cons_self) ?_
              simp only [step_put, List.erase_cons_head]
              rw [upd_comm _ _ _ _ _ hk]
              simpa [step_put] using hr'
    | perm p hp =>
      rcases ih with h1 | ⟨x, i, hx, hi, him, Q, hQ, hr'⟩
      · exact .inl h1
      · exact .inr ⟨x, i, hx, hi, hp.mem_iff.1 him, Q, hQ.trans (hp.erase i).subperm, hr'⟩

/-! ## The bracket -/

/-- The configurations reachable from `⟨a, P⟩`. -/
def Funl (a : St) (P : List KIn) : PSet St KIn := fun c => PReach kvB ⟨a, P⟩ c

/-- The configurations reachable from `a` with some of `P` pending. -/
def Fall (a : St) (P : List KIn) : PSet St KIn :=
  fun c => ∃ Q, Q.Subperm P ∧ PReach kvB ⟨a, Q⟩ c

/-- **The Go state `(a, P)` brackets the model's set `S`.** -/
def Sim (a : St) (P : List KIn) (S : PSet St KIn) : Prop :=
  (∀ c, Funl a P c → S c) ∧ (∀ c, S c → Fall a P c)

theorem Fall_reach {a : St} {P : List KIn} {c c' : PCfg St KIn} (h : Fall a P c)
    (hr : PReach kvB c c') : Fall a P c' := by
  obtain ⟨Q, hQ, h⟩ := h
  exact ⟨Q, hQ, h.trans hr⟩

theorem sim_init : Sim kvB.init [] (pInit kvB) := by
  constructor
  · intro c h
    show c = ⟨kvB.init, []⟩
    suffices ∀ c₀ c', PReach kvB c₀ c' → c₀.pend = [] → c' = c₀ from
      (this _ _ h rfl)
    intro c₀ c' hr
    induction hr with
    | refl => intro _; rfl
    | @step c c₁ c₂ hs _ ih =>
      intro hp
      cases hs with
      | apply j hj => simp [hp] at hj
      | perm p hq =>
        rw [hp] at hq
        have := hq.eq_nil
        subst this
        rw [ih rfl, ← hp]
  · intro c h
    rw [show c = ⟨kvB.init, []⟩ from h]
    exact ⟨[], List.Subperm.refl _, .refl _⟩

/-! ## The Go step -/

/-- kit.go's `step` on the decoded answer: its verdict and next state. -/
def goStep (a : St) (P : List KIn) : KIn → Ans KOut → Option (St × List KIn)
  | i, .err => if isPut i then some (a, P ++ [i]) else some (a, P)
  | ⟨.put k x, h⟩, .ok (.got none) => some (upd a k ⟨x, h.2⟩, P)
  | ⟨.put _ _, _⟩, .ok (.got (some _)) => none
  | _, .ok .bad => none
  | ⟨.get k, _⟩, .ok (.got none) => if a k = none then some (a, P) else none
  | ⟨.get k, hk⟩, .ok (.got (some x)) =>
    if a k = some x then some (a, P)
    else if (⟨.put k x.1, ⟨hk, x.2⟩⟩ : KIn) ∈ P then
      some (upd a k x, P.erase ⟨.put k x.1, ⟨hk, x.2⟩⟩)
    else none

theorem pstep_inv {c c₁ : PCfg St KIn} {i : KIn} {o : Ans KOut} (h : PStep kvB c i o c₁) :
    (o = .ok (kvB.step i c.st).2 ∧ c₁ = ⟨(kvB.step i c.st).1, c.pend⟩) ∨
    (o = .err ∧ isPut i = true ∧ c₁ = ⟨c.st, i :: c.pend⟩) ∨
    (o = .err ∧ isPut i = false ∧ c₁ = c) := by
  cases h with
  | ok => exact .inl ⟨rfl, rfl⟩
  | errW hw _ => exact .inr (.inl ⟨rfl, hw, rfl⟩)
  | errR hw _ => exact .inr (.inr ⟨rfl, hw, rfl⟩)
  | obs _ hob _ => exact absurd hob (by simp [kvB])

theorem get_step_eq (k : GoString) (hk : inOk (.get k)) (c : PCfg St KIn) :
    (⟨(kvB.step ⟨.get k, hk⟩ c.st).1, c.pend⟩ : PCfg St KIn) = c := rfl

/-- The model's next set, when the Go step allows the operation: nonempty and bracketed. -/
theorem sim_some {a : St} {P : List KIn} {S : PSet St KIn} (hS : Sim a P S) {i : KIn}
    {o : Ans KOut} {a' : St} {P' : List KIn} (hg : goStep a P i o = some (a', P')) :
    (∃ c, ppost kvB S i o c) ∧ Sim a' P' (ppost kvB S i o) := by
  have hbase : S ⟨a, P⟩ := hS.1 _ (.refl _)
  have hF : ∀ c₀ c, S c₀ → PReach kvB c₀ c → Fall a P c := fun c₀ c h hr =>
    Fall_reach (hS.2 _ h) hr
  -- the next set is bracketed by `(a', P')` if its lower bound has a first configuration
  suffices hlow : (∀ c, Funl a' P' c → ppost kvB S i o c) ∧ (∀ c, ppost kvB S i o c → Fall a' P' c) by
    exact ⟨⟨_, hlow.1 _ (.refl _)⟩, hlow⟩
  match o, i, hg with
  | .err, i, hg =>
    unfold goStep at hg
    by_cases hp : isPut i = true
    · simp only [hp, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      constructor
      · intro c h
        exact ⟨⟨a, P⟩, ⟨a, P⟩, ⟨a, i :: P⟩, hbase, .refl _, .errW _ _ hp rfl,
          .step (.perm _ _ (List.perm_append_singleton _ _)) h⟩
      · rintro c' ⟨c₀, c, c₁, h0, hr, hs, hr'⟩
        obtain ⟨Q, hQ, hq⟩ := hF _ _ h0 hr
        rcases pstep_inv hs with ⟨he, _⟩ | ⟨_, _, rfl⟩ | ⟨_, hw, _⟩
        · cases he
        · refine ⟨i :: Q, ?_, (reach_cons i hq).trans hr'⟩
          exact ((List.subperm_cons _).2 hQ).trans (List.perm_append_singleton _ _).symm.subperm
        · simp [hp] at hw
    · simp only [hp, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, Bool.false_eq_true] at hg
      obtain ⟨rfl, rfl⟩ := hg
      have hp' : isPut i = false := by simpa using hp
      constructor
      · intro c h
        exact ⟨⟨a, P⟩, ⟨a, P⟩, ⟨a, P⟩, hbase, .refl _, .errR _ _ hp' rfl, h⟩
      · rintro c' ⟨c₀, c, c₁, h0, hr, hs, hr'⟩
        rcases pstep_inv hs with ⟨he, _⟩ | ⟨_, hw, _⟩ | ⟨_, _, rfl⟩
        · cases he
        · simp [hp'] at hw
        · exact Fall_reach (hF _ _ h0 hr) hr'
  | .ok (.got none), ⟨.put k x, h⟩, hg =>
    simp only [goStep, Option.some.injEq, Prod.mk.injEq] at hg
    obtain ⟨rfl, rfl⟩ := hg
    constructor
    · intro c hc
      exact ⟨⟨a, P⟩, ⟨a, P⟩, _, hbase, .refl _, .ok _ _ rfl, hc⟩
    · rintro c' ⟨c₀, c, c₁, h0, hr, hs, hr'⟩
      obtain ⟨Q, hQ, hq⟩ := hF _ _ h0 hr
      rcases pstep_inv hs with ⟨_, rfl⟩ | ⟨he, _⟩ | ⟨he, _⟩
      · obtain ⟨Q₂, hQ₂, hq₂⟩ := reach_put k ⟨x, h.2⟩ hq
        exact ⟨Q₂, hQ₂.trans hQ, hq₂.trans (by simpa [step_put] using hr')⟩
      · cases he
      · cases he
  | .ok (.got none), ⟨.get k, hk⟩, hg =>
    simp only [goStep] at hg
    split at hg
    · rename_i hak
      simp only [Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      constructor
      · intro c hc
        refine ⟨⟨a, P⟩, ⟨a, P⟩, ⟨a, P⟩, hbase, .refl _, ?_, hc⟩
        have := PStep.ok (P := kvB) ⟨a, P⟩ ⟨.get k, hk⟩ rfl
        simpa [step_get, hak] using this
      · rintro c' ⟨c₀, c, c₁, h0, hr, hs, hr'⟩
        rcases pstep_inv hs with ⟨_, rfl⟩ | ⟨he, _⟩ | ⟨he, _⟩
        · exact Fall_reach (hF _ _ h0 hr) hr'
        · cases he
        · cases he
    · cases hg
  | .ok (.got (some x)), ⟨.get k, hk⟩, hg =>
    simp only [goStep] at hg
    split at hg
    · rename_i hak
      simp only [Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      constructor
      · intro c hc
        refine ⟨⟨a, P⟩, ⟨a, P⟩, ⟨a, P⟩, hbase, .refl _, ?_, hc⟩
        have := PStep.ok (P := kvB) ⟨a, P⟩ ⟨.get k, hk⟩ rfl
        simpa [step_get, hak] using this
      · rintro c' ⟨c₀, c, c₁, h0, hr, hs, hr'⟩
        rcases pstep_inv hs with ⟨_, rfl⟩ | ⟨he, _⟩ | ⟨he, _⟩
        · exact Fall_reach (hF _ _ h0 hr) hr'
        · cases he
        · cases he
    · rename_i hak
      split at hg
      · rename_i hmem
        simp only [Option.some.injEq, Prod.mk.injEq] at hg
        obtain ⟨rfl, rfl⟩ := hg
        constructor
        · intro c hc
          have hf : PReach kvB ⟨a, P⟩ ⟨upd a k x, P.erase ⟨.put k x.1, ⟨hk, x.2⟩⟩⟩ := by
            have := PReach.single (PSilent.apply (P := kvB) ⟨a, P⟩ _ hmem)
            exact this
          refine ⟨⟨a, P⟩, ⟨upd a k x, P.erase _⟩, ⟨upd a k x, P.erase _⟩, hbase, hf, ?_, hc⟩
          have := PStep.ok (P := kvB) ⟨upd a k x, P.erase ⟨.put k x.1, ⟨hk, x.2⟩⟩⟩ ⟨.get k, hk⟩ rfl
          simpa [step_get, upd_get] using this
        · rintro c' ⟨c₀, c, c₁, h0, hr, hs, hr'⟩
          obtain ⟨Q, hQ, hq⟩ := hF _ _ h0 hr
          rcases pstep_inv hs with ⟨he, rfl⟩ | ⟨he, _⟩ | ⟨he, _⟩
          · simp only [step_get, Ans.ok.injEq, KOut.got.injEq] at he
            rcases reach_key k hq with h1 | ⟨y, j, hy, hj, -, Q₂, hQ₂, hq₂⟩
            · exact absurd (h1.symm.trans he.symm) hak
            · have hxy : y = x := Option.some.inj (hy.symm.trans he.symm)
              subst hxy
              have hj' : j = ⟨.put k y.1, ⟨hk, y.2⟩⟩ := Subtype.ext hj
              subst hj'
              exact ⟨Q₂, hQ₂.trans (hQ.erase _), hq₂.trans hr'⟩
          · cases he
          · cases he
      · cases hg

/-- The model's next set, when the Go step refuses the operation: empty. -/
theorem sim_none {a : St} {P : List KIn} {S : PSet St KIn} (hS : Sim a P S) {i : KIn}
    {o : Ans KOut} (hg : goStep a P i o = none) : ¬ ∃ c, ppost kvB S i o c := by
  rintro ⟨c', c₀, c, c₁, h0, hr, hs, -⟩
  obtain ⟨Q, hQ, hq⟩ := Fall_reach (hS.2 _ h0) hr
  rcases pstep_inv hs with ⟨he, -⟩ | ⟨rfl, hw, -⟩ | ⟨rfl, hw, -⟩
  · subst he
    obtain ⟨k | ⟨k, x⟩, h⟩ := i
    · simp only [step_get, goStep] at hg
      cases hv : c.st k with
      | none =>
        rw [hv] at hg
        simp only at hg
        split at hg
        · cases hg
        · rename_i hak
          rcases reach_key k hq with h1 | ⟨y, j, hy, -⟩
          · exact hak (h1.symm.trans hv)
          · rw [hv] at hy; cases hy
      | some x =>
        rw [hv] at hg
        simp only at hg
        split at hg
        · cases hg
        · rename_i hak
          split at hg
          · cases hg
          · rename_i hmem
            rcases reach_key k hq with h1 | ⟨y, j, hy, hj, hjm, -⟩
            · exact hak (h1.symm.trans hv)
            · have hxy : y = x := Option.some.inj (hy.symm.trans hv)
              subst hxy
              have hj' : j = ⟨.put k y.1, ⟨h, y.2⟩⟩ := Subtype.ext hj
              subst hj'
              exact hmem (hQ.subset hjm)
    · simp [step_put, goStep] at hg
  · simp [goStep, hw] at hg
  · simp [goStep, hw] at hg

/-- **The simulation**: on a bracketed set, the model allows `(i, o)` exactly when the Go step
does, and its next set is bracketed by the Go step's next state. -/
theorem sim_step {a : St} {P : List KIn} {S : PSet St KIn} (hS : Sim a P S) (i : KIn)
    (o : Ans KOut) :
    ((pSeq kvB).step S (i, o)).isSome = (goStep a P i o).isSome ∧
    ∀ a' P' S', goStep a P i o = some (a', P') → (pSeq kvB).step S (i, o) = some S' →
      Sim a' P' S' := by
  cases hg : goStep a P i o with
  | none =>
    refine ⟨?_, fun _ _ _ h => by cases h⟩
    have := sim_none hS hg
    simp only [pSeq, Option.isSome_none]
    rw [if_neg this]
    rfl
  | some r =>
    obtain ⟨a', P'⟩ := r
    obtain ⟨hne, hsim⟩ := sim_some hS hg
    refine ⟨?_, ?_⟩
    · simp only [pSeq, Option.isSome_some]
      rw [if_pos hne]
      rfl
    · intro a'' P'' S' he hs
      cases he
      have := pSeq_step_some hs
      subst this
      exact hsim

end github_com.despreston.go_craq.examples.craqnet
end Perennial
