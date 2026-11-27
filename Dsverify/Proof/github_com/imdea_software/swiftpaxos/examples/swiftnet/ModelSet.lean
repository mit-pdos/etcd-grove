/-
The swiftpaxos kit's key-value map with pending puts, pure (kit.go's `State`/`step`;
notes/dsv-swiftpaxos.md, "The kit over remote"; as dsv-paxos's and dsv-rabia's `ModelSet.lean`):

* **The store** `swB`: linkv's pending-writes store (`linkv.PendSpec`) of the key-value map over the
  kit's inputs `KIn` (`In{Put, K, V}`: a key below `NKeys = 2`, a bounded value) and bounded outputs
  `BStr` (a get answers the key's value, `""` for none; a put answers `""`). A put is a write: one of
  unknown outcome is pending, and may take effect later, once, or never.
* **The set semantics** `swSet cur pend`: per key `k`, the configurations `(x, Q)` with
  `x = cur[k] ∧ Q ⊆ pend[k]` or `x ∈ pend[k] ∧ Q ⊆ pend[k] − x` (multisets; downward closed in the
  pending puts: a pending put may never take effect), as dsv-paxos's `woSet`.
* **The simulation** `Sim cur pend S`: the model's state `S` (the exact set of configurations the
  history may have reached, `linkv.pSeq`) lies within `swSet cur pend`, holds the configuration
  `(cur, pend)` with every pending put still pending (`Full`), and is closed under late effects.
  `stepG_sim`: **kit.go's `step` (`stepG`) gives porcupine's verdict exactly, and keeps the
  simulation.** The set is not a function of the Go state (`equal_unsound`, below): no `Equal`
  comparing model values is sound for porcupine's `equalSpec`, which is why kit.go's `Equal` is
  always `false` (`dff42254a2`; see `ModelProof.lean`'s header).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.PendModel
public import Perennial.Std.ByteString
public import Batteries.Data.List.Perm

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

open EtcdGrove EtcdGrove.linkv

/-! ## The store -/

/-- A bounded string: the store's values and outputs. -/
abbrev BStr := {s : GoString // s.length < 2 ^ 48}

/-- The empty string, bounded. -/
def bnil : BStr := ⟨[], by decide⟩

/-- An input (kit.go's `In{Put, K, V}`): its key below `NKeys = 2`, its value bounded. -/
def inB (x : Bool × Nat × GoString) : Prop := x.2.1 < 2 ∧ x.2.2.length < 2 ^ 48

abbrev KIn := {x : Bool × Nat × GoString // inB x}

/-- `KIn`'s `BEq` is its decidable equality's (the instance linkv's pending lists erase with). -/
@[reducible] instance (priority := high) KIn.beq : BEq KIn := instBEqOfDecidableEq

abbrev KIn.put (i : KIn) : Bool := i.1.1
abbrev KIn.key (i : KIn) : Nat := i.1.2.1
abbrev KIn.val (i : KIn) : GoString := i.1.2.2

/-- An input's value, bounded. -/
def KIn.bval (i : KIn) : BStr := ⟨i.val, i.2.2⟩

theorem KIn.key_lt (i : KIn) : i.key < 2 := i.2.1

/-- The store's state: each key's value. -/
abbrev St := Nat → BStr

/-- `σ` with `k` at `v`. -/
def upd (σ : St) (k : Nat) (v : BStr) : St := fun k' => if k' = k then v else σ k'

theorem upd_same (σ : St) (k : Nat) (v : BStr) : upd σ k v k = v := by simp [upd]

theorem upd_ne (σ : St) {k k' : Nat} (v : BStr) (h : k' ≠ k) : upd σ k v k' = σ k' := by
  simp [upd, h]

/-- **The key-value map with failed puts** (linkv's pending-writes store): a put sets its key and
answers `""`, a get answers its key's value; a put is a write. -/
def swB : PendSpec St KIn BStr where
  init := fun _ => bnil
  step i σ := if i.put then (upd σ i.key i.bval, bnil) else (σ, σ i.key)
  isWrite i := i.put

theorem swB_put (i : KIn) (h : i.put = true) (σ : St) :
    swB.step i σ = (upd σ i.key i.bval, bnil) := by
  simp [swB, h]

theorem swB_get (i : KIn) (h : i.put = false) (σ : St) : swB.step i σ = (σ, σ i.key) := by
  simp [swB, h]

/-! ## The set semantics -/

/-- The values of the puts of `l` at key `k`. -/
def proj (l : List KIn) (k : Nat) : List GoString :=
  (l.filter (fun i => decide (i.key = k))).map KIn.val

theorem proj_perm {l l' : List KIn} (h : l.Perm l') (k : Nat) : (proj l k).Perm (proj l' k) :=
  (h.filter _).map _

theorem proj_cons (i : KIn) (l : List KIn) (k : Nat) :
    proj (i :: l) k = if i.key = k then i.val :: proj l k else proj l k := by
  by_cases h : i.key = k <;> simp [proj, h]

/-- `l` without `j`, at `j`'s key: the values less `j`'s, up to order. -/
theorem proj_erase_same {l : List KIn} {j : KIn} (hj : j ∈ l) :
    (proj l j.key).Perm (j.val :: proj (l.erase j) j.key) := by
  have := proj_perm (List.perm_cons_erase hj) j.key
  simpa only [proj_cons, ↓reduceIte] using this

/-- `l` without `j`, at another key: the same values, up to order. -/
theorem proj_erase_ne {l : List KIn} {j : KIn} (hj : j ∈ l) {k : Nat} (hk : j.key ≠ k) :
    (proj l k).Perm (proj (l.erase j) k) := by
  have := proj_perm (List.perm_cons_erase hj) k
  simpa only [proj_cons, hk, ↓reduceIte] using this

/-- One key's configuration `(x, Q)` for the model's value `cur` and pending puts `P`: `cur` with
some of `P` pending, or some `x` of `P` taken effect with some of the others pending. -/
def keyOk (x : GoString) (Q : List GoString) (cur : GoString) (P : List GoString) : Prop :=
  (x = cur ∧ Q.Subperm P) ∨ (x ∈ P ∧ Q.Subperm (P.erase x))

/-- **The configurations the model's state `State{cur, pend}` stands for**: pending inputs are
puts, and each key's configuration is `keyOk` (see the file header). -/
def swSet (cur : List GoString) (pend : List (List GoString)) : PSet St KIn := fun c =>
  (∀ i ∈ c.pend, i.put = true) ∧
    ∀ k, k < 2 → keyOk (c.st k).1 (proj c.pend k) (cur.getD k []) (pend.getD k [])

/-- The configuration `(cur, pend)` itself: each key at `cur`, all its pending puts pending. -/
def Full (cur : List GoString) (pend : List (List GoString)) (c : PCfg St KIn) : Prop :=
  ∀ k, k < 2 → (c.st k).1 = cur.getD k [] ∧ (proj c.pend k).Perm (pend.getD k [])

/-- **The simulation**: the model's state `S` lies within `swSet cur pend`, holds `(cur, pend)`,
and is closed under late effects. -/
structure Sim (cur : List GoString) (pend : List (List GoString)) (S : PSet St KIn) : Prop where
  sub : ∀ c, S c → swSet cur pend c
  full : ∃ c, S c ∧ Full cur pend c
  closed : PSet.Closed swB S

theorem keyOk_perm {x cur : GoString} {Q Q' P : List GoString} (h : Q.Perm Q') :
    keyOk x Q cur P ↔ keyOk x Q' cur P := by
  unfold keyOk; rw [h.subperm_right, h.subperm_right]

theorem keyOk_sub {x cur : GoString} {Q P : List GoString} (h : keyOk x Q cur P) :
    Q.Subperm P := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact h
  · exact h.trans (List.erase_subperm _ _)

theorem keyOk_val {x cur : GoString} {Q P : List GoString} (h : keyOk x Q cur P) :
    x = cur ∨ x ∈ P := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · exact .inl h
  · exact .inr h

/-- A pending put `v` takes effect. -/
theorem keyOk_apply {x v cur : GoString} {Q P : List GoString} (h : keyOk x (v :: Q) cur P) :
    keyOk v Q cur P := by
  right
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · refine ⟨h.subset List.mem_cons_self, ?_⟩
    have := List.Subperm.erase v h
    rwa [List.erase_cons_head] at this
  · refine ⟨List.mem_of_mem_erase (h.subset List.mem_cons_self), ?_⟩
    have := List.Subperm.erase v h
    rw [List.erase_cons_head] at this
    exact this.trans (by rw [List.erase_comm]; exact List.erase_subperm _ _)

/-- A new pending put `v`. -/
theorem keyOk_push {x v cur : GoString} {Q P : List GoString} (h : keyOk x Q cur P) :
    keyOk x (v :: Q) cur (P ++ [v]) := by
  have hP : (P ++ [v]).Perm (v :: P) := List.perm_append_singleton v P
  rcases h with ⟨h1, h⟩ | ⟨h1, h⟩
  · exact .inl ⟨h1, ((List.subperm_cons v).2 h).trans hP.symm.subperm⟩
  · refine .inr ⟨List.mem_append_left _ h1, ?_⟩
    rw [List.erase_append_left _ h1]
    exact ((List.subperm_cons v).2 h).trans (List.perm_append_singleton v _).symm.subperm

theorem ite_yes {α : Type} {p : Prop} [Decidable p] {a b : α} (h : p) :
    (if p then a else b) = a := by simp [h]

theorem ite_no {α : Type} {p : Prop} [Decidable p] {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by simp [h]

theorem getD_set_eq {α : Type} (l : List α) (n : Nat) (x d : α) (h : n < l.length) :
    (l.set n x).getD n d = x := by
  simp [List.getD, h]

theorem getD_set_ne {α : Type} (l : List α) {n m : Nat} (x d : α) (h : n ≠ m) :
    (l.set n x).getD m d = l.getD m d := by
  simp [List.getD, h]

/-! ## Late effects -/

theorem swSet_silent {cur : List GoString} {pend : List (List GoString)} {c c' : PCfg St KIn}
    (hs : PSilent swB c c') (hc : swSet cur pend c) : swSet cur pend c' := by
  obtain ⟨hput, hk⟩ := hc
  cases hs with
  | apply j hj =>
    have hjp := hput j hj
    rw [swB_put j hjp]
    dsimp only
    refine ⟨fun i hi => hput i (List.mem_of_mem_erase hi), fun k hkl => ?_⟩
    show keyOk (upd c.st j.key j.bval k).1 (proj (c.pend.erase j) k) (cur.getD k []) (pend.getD k [])
    by_cases hkj : k = j.key
    · subst hkj
      rw [upd_same]
      have h := hk j.key hkl
      rw [keyOk_perm (proj_erase_same hj)] at h
      exact keyOk_apply h
    · rw [upd_ne _ _ hkj, ← keyOk_perm (proj_erase_ne hj (Ne.symm hkj))]
      exact hk k hkl
  | perm p hp =>
    refine ⟨fun i hi => hput i (hp.subset hi), fun k hkl => ?_⟩
    rw [keyOk_perm (proj_perm hp k)]
    exact hk k hkl

theorem swSet_reach {cur : List GoString} {pend : List (List GoString)} {c c' : PCfg St KIn}
    (hr : PReach swB c c') (hc : swSet cur pend c) : swSet cur pend c' := by
  induction hr with
  | refl => exact hc
  | step hs _ ih => exact ih (swSet_silent hs hc)

/-! ## One operation -/

theorem pstep_ok_inv {c c₁ : PCfg St KIn} {i : KIn} {w : BStr} (h : PStep swB c i (.ok w) c₁) :
    w = (swB.step i c.st).2 ∧ c₁ = ⟨(swB.step i c.st).1, c.pend⟩ := by
  cases h with
  | ok _ => exact ⟨rfl, rfl⟩
  | obs _ h _ => simp [swB] at h

theorem pstep_err_inv {c c₁ : PCfg St KIn} {i : KIn} (h : PStep swB c i .err c₁) :
    (i.put = true ∧ c₁ = ⟨c.st, i :: c.pend⟩) ∨ (i.put = false ∧ c₁ = c) := by
  cases h with
  | errW h _ => exact .inl ⟨h, rfl⟩
  | errR h _ => exact .inr ⟨h, rfl⟩

/-- A step that keeps the simulation: every successor of `S`'s configurations is in `swSet cur'
pend'`, and some is `(cur', pend')`. -/
theorem sim_step {cur cur' : List GoString} {pend pend' : List (List GoString)} {S : PSet St KIn}
    (hS : Sim cur pend S) (i : KIn) (a : Ans BStr)
    (hsub : ∀ c c₁, S c → PStep swB c i a c₁ → swSet cur' pend' c₁)
    (hfull : ∃ c c₁, S c ∧ PStep swB c i a c₁ ∧ Full cur' pend' c₁) :
    ∃ S', (pSeq swB).step S (i, a) = some S' ∧ Sim cur' pend' S' := by
  obtain ⟨c, c₁, hc, hst, hf⟩ := hfull
  obtain ⟨S', hS', hc₁⟩ := pSeq_step_of_pstep hc hst (.refl _)
  refine ⟨S', hS', ⟨fun c' hc' => ?_, ⟨c₁, hc₁, hf⟩, pSeq_step_closed hS'⟩⟩
  rw [pSeq_step_some hS'] at hc'
  obtain ⟨c0, c2, c3, h0, hr, hst', hr'⟩ := hc'
  exact swSet_reach hr' (hsub c2 c3 (hS.closed _ _ h0 hr) hst')

/-- A step no configuration of `S` can make: porcupine refuses it. -/
theorem sim_none {cur : List GoString} {pend : List (List GoString)} {S : PSet St KIn}
    (hS : Sim cur pend S) (i : KIn) (a : Ans BStr)
    (h : ∀ c c₁, S c → ¬ PStep swB c i a c₁) : (pSeq swB).step S (i, a) = none := by
  simp only [pSeq]
  split
  · next hc =>
    obtain ⟨c', c0, c, c1, h0, hr, hst, -⟩ := hc
    exact absurd hst (h c c1 (hS.closed _ _ h0 hr))
  · rfl

/-! ## kit.go's `step` -/

/-- **kit.go's `step`** on the model's pure state `(Cur, Pend)`, for an input `i` and an output
`Out{u, w}`: its verdict and next state. -/
def stepG (cur : List GoString) (pend : List (List GoString)) (i : KIn) (u : Bool) (w : GoString) :
    Bool × List GoString × List (List GoString) :=
  if u then
    (if i.put then (true, cur, pend.set i.key (pend.getD i.key [] ++ [i.val])) else (true, cur, pend))
  else if i.put then (decide (w = []), cur.set i.key i.val, pend)
  else if w = cur.getD i.key [] then (true, cur, pend)
  else if w ∈ pend.getD i.key [] then
    (true, cur.set i.key w, pend.set i.key ((pend.getD i.key []).erase w))
  else (false, cur, pend)

section cases
variable {cur : List GoString} {pend : List (List GoString)} {S : PSet St KIn}

theorem step_errW (hp : pend.length = 2) (hS : Sim cur pend S) (i : KIn) (hi : i.put = true) :
    ∃ S', (pSeq swB).step S (i, .err) = some S' ∧
      Sim cur (pend.set i.key (pend.getD i.key [] ++ [i.val])) S' := by
  have hkl : i.key < pend.length := hp ▸ i.key_lt
  refine sim_step hS i .err (fun c c₁ hc hst => ?_) ?_
  · rcases pstep_err_inv hst with ⟨-, rfl⟩ | ⟨h, -⟩
    · obtain ⟨hput, hk⟩ := hS.sub c hc
      refine ⟨fun j hj => ?_, fun k hk2 => ?_⟩
      · rcases List.mem_cons.1 hj with rfl | hj
        · exact hi
        · exact hput j hj
      simp only
      rw [proj_cons]
      by_cases hik : i.key = k
      · subst hik
        rw [ite_yes rfl, getD_set_eq _ _ _ _ hkl]
        exact keyOk_push (hk _ hk2)
      · rw [ite_no hik, getD_set_ne _ _ _ hik]
        exact hk k hk2
    · rw [hi] at h; cases h
  · obtain ⟨c, hc, hf⟩ := hS.full
    refine ⟨c, ⟨c.st, i :: c.pend⟩, hc, .errW c i hi rfl, fun k hk2 => ?_⟩
    obtain ⟨h1, h2⟩ := hf k hk2
    refine ⟨h1, ?_⟩
    simp only
    rw [proj_cons]
    by_cases hik : i.key = k
    · subst hik
      rw [ite_yes rfl, getD_set_eq _ _ _ _ hkl]
      exact (h2.cons _).trans (List.perm_append_singleton _ _).symm
    · rw [ite_no hik, getD_set_ne _ _ _ hik]
      exact h2

theorem step_errR (hS : Sim cur pend S) (i : KIn) (hi : i.put = false) :
    ∃ S', (pSeq swB).step S (i, .err) = some S' ∧ Sim cur pend S' := by
  refine sim_step hS i .err (fun c c₁ hc hst => ?_) ?_
  · rcases pstep_err_inv hst with ⟨h, -⟩ | ⟨-, rfl⟩
    · rw [hi] at h; cases h
    · exact hS.sub _ hc
  · obtain ⟨c, hc, hf⟩ := hS.full
    exact ⟨c, c, hc, .errR c i hi rfl, hf⟩

theorem step_put_no (hS : Sim cur pend S) (i : KIn) (hi : i.put = true) (w : BStr)
    (hw : w.1 ≠ []) : (pSeq swB).step S (i, .ok w) = none := by
  refine sim_none hS i _ (fun c c₁ _ hst => ?_)
  obtain ⟨e, -⟩ := pstep_ok_inv hst
  rw [swB_put i hi] at e
  exact hw (by rw [e]; rfl)

theorem step_put_ok (hc : cur.length = 2) (hS : Sim cur pend S) (i : KIn) (hi : i.put = true)
    (w : BStr) (hw : w.1 = []) :
    ∃ S', (pSeq swB).step S (i, .ok w) = some S' ∧ Sim (cur.set i.key i.val) pend S' := by
  have hkl : i.key < cur.length := hc ▸ i.key_lt
  have hwb : w = bnil := Subtype.ext hw
  subst hwb
  refine sim_step hS i _ (fun c c₁ hc' hst => ?_) ?_
  · obtain ⟨-, rfl⟩ := pstep_ok_inv hst
    obtain ⟨hput, hk⟩ := hS.sub c hc'
    rw [swB_put i hi]
    refine ⟨hput, fun k hk2 => ?_⟩
    show keyOk (upd c.st i.key i.bval k).1 (proj c.pend k) _ _
    by_cases hik : k = i.key
    · subst hik
      rw [upd_same, getD_set_eq _ _ _ _ hkl]
      exact .inl ⟨rfl, keyOk_sub (hk _ hk2)⟩
    · rw [upd_ne _ _ hik, getD_set_ne _ _ _ (Ne.symm hik)]
      exact hk k hk2
  · obtain ⟨c, hc', hf⟩ := hS.full
    have h := PStep.ok (P := swB) c i rfl
    rw [swB_put i hi] at h
    refine ⟨c, _, hc', h, fun k hk2 => ?_⟩
    obtain ⟨h1, h2⟩ := hf k hk2
    refine ⟨?_, h2⟩
    show (upd c.st i.key i.bval k).1 = _
    by_cases hik : k = i.key
    · subst hik
      rw [upd_same, getD_set_eq _ _ _ _ hkl]
      rfl
    · rw [upd_ne _ _ hik, getD_set_ne _ _ _ (Ne.symm hik)]
      exact h1

theorem step_get_cur (hS : Sim cur pend S) (i : KIn) (hi : i.put = false) (w : BStr)
    (hw : w.1 = cur.getD i.key []) :
    ∃ S', (pSeq swB).step S (i, .ok w) = some S' ∧ Sim cur pend S' := by
  refine sim_step hS i _ (fun c c₁ hc' hst => ?_) ?_
  · obtain ⟨-, rfl⟩ := pstep_ok_inv hst
    rw [swB_get i hi]
    exact hS.sub c hc'
  · obtain ⟨c, hc', hf⟩ := hS.full
    have h := PStep.ok (P := swB) c i rfl
    rw [swB_get i hi] at h
    have e : c.st i.key = w := Subtype.ext ((hf _ i.key_lt).1.trans hw.symm)
    rw [e] at h
    exact ⟨c, c, hc', h, hf⟩

theorem step_get_pend (hc : cur.length = 2) (hp : pend.length = 2) (hS : Sim cur pend S)
    (i : KIn) (hi : i.put = false) (w : BStr) (hw : w.1 ≠ cur.getD i.key [])
    (hm : w.1 ∈ pend.getD i.key []) :
    ∃ S', (pSeq swB).step S (i, .ok w) = some S' ∧
      Sim (cur.set i.key w.1) (pend.set i.key ((pend.getD i.key []).erase w.1)) S' := by
  have hkl : i.key < cur.length := hc ▸ i.key_lt
  have hkp : i.key < pend.length := hp ▸ i.key_lt
  refine sim_step hS i _ (fun c c₁ hc' hst => ?_) ?_
  · obtain ⟨e, rfl⟩ := pstep_ok_inv hst
    obtain ⟨hput, hk⟩ := hS.sub c hc'
    rw [swB_get i hi] at e ⊢
    dsimp only at e
    refine ⟨hput, fun k hk2 => ?_⟩
    show keyOk (c.st k).1 (proj c.pend k) _ _
    by_cases hik : k = i.key
    · subst hik
      rw [getD_set_eq _ _ _ _ hkl, getD_set_eq _ _ _ _ hkp]
      rcases hk _ hk2 with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd (by rw [e]; exact h1) hw
      · subst e
        exact .inl ⟨rfl, h2⟩
    · rw [getD_set_ne _ _ _ (Ne.symm hik), getD_set_ne _ _ _ (Ne.symm hik)]
      exact hk k hk2
  · obtain ⟨c0, hc0, hf⟩ := hS.full
    obtain ⟨hput, -⟩ := hS.sub c0 hc0
    have hmp : w.1 ∈ proj c0.pend i.key := (hf _ i.key_lt).2.symm.subset hm
    obtain ⟨j, hjm, hjv⟩ := List.mem_map.1 hmp
    obtain ⟨hj, hjk⟩ := List.mem_filter.1 hjm
    have hjk : j.key = i.key := of_decide_eq_true hjk
    have hjp := hput j hj
    have hc1 := hS.closed.apply hc0 hj
    rw [swB_put j hjp] at hc1
    have h := PStep.ok (P := swB) ⟨upd c0.st j.key j.bval, c0.pend.erase j⟩ i rfl
    rw [swB_get i hi] at h
    have e : upd c0.st j.key j.bval i.key = w := by
      rw [← hjk, upd_same]; exact Subtype.ext hjv
    simp only at h
    rw [e] at h
    refine ⟨_, _, hc1, h, fun k hk2 => ?_⟩
    obtain ⟨h1, h2⟩ := hf k hk2
    show (upd c0.st j.key j.bval k).1 = _ ∧ (proj (c0.pend.erase j) k).Perm _
    by_cases hik : k = i.key
    · subst hik
      rw [getD_set_eq _ _ _ _ hkl, getD_set_eq _ _ _ _ hkp, e]
      refine ⟨rfl, ?_⟩
      have h3 := proj_erase_same hj
      rw [hjk, hjv] at h3
      have h3 := h3.symm.trans h2
      have h4 := h3.erase w.1
      rwa [List.erase_cons_head] at h4
    · rw [getD_set_ne _ _ _ (Ne.symm hik), getD_set_ne _ _ _ (Ne.symm hik),
        upd_ne _ _ (by rw [hjk]; exact hik)]
      exact ⟨h1, (proj_erase_ne hj (by rw [hjk]; exact Ne.symm hik)).symm.trans h2⟩

theorem step_get_no (hS : Sim cur pend S) (i : KIn) (hi : i.put = false) (w : BStr)
    (hw : w.1 ≠ cur.getD i.key []) (hm : w.1 ∉ pend.getD i.key []) :
    (pSeq swB).step S (i, .ok w) = none := by
  refine sim_none hS i _ (fun c c₁ hc' hst => ?_)
  obtain ⟨e, -⟩ := pstep_ok_inv hst
  rw [swB_get i hi] at e
  obtain ⟨-, hk⟩ := hS.sub c hc'
  rcases keyOk_val (hk _ i.key_lt) with h | h
  · exact hw (by rw [e]; exact h)
  · exact hm (by rw [e]; exact h)

end cases

/-- porcupine's answer for kit.go's output `Out{u, w}`: unknown, or `w`. -/
def ansOf (u : Bool) (w : BStr) : Ans BStr := if u then .err else .ok w

/-- **kit.go's `step` is the pending model's step** on a simulated set: its verdict is
porcupine's, and its next state simulates porcupine's next set. -/
theorem stepG_sim {cur : List GoString} {pend : List (List GoString)} {S : PSet St KIn}
    (hc : cur.length = 2) (hp : pend.length = 2) (hS : Sim cur pend S) (i : KIn) (u : Bool)
    (w : BStr) (hu : u = true → w.1 = []) :
    ((pSeq swB).step S (i, ansOf u w)).isSome = (stepG cur pend i u w.1).1 ∧
      ∀ S', (pSeq swB).step S (i, ansOf u w) = some S' →
        Sim (stepG cur pend i u w.1).2.1 (stepG cur pend i u w.1).2.2 S' := by
  have fin : ∀ {o : Option (PSet St KIn)} {S₀ : PSet St KIn} {cur' pend'},
      o = some S₀ → Sim cur' pend' S₀ →
      o.isSome = true ∧ ∀ S', o = some S' → Sim cur' pend' S' := by
    intro o S₀ cur' pend' h hs
    subst h
    exact ⟨rfl, fun S' h' => by cases h'; exact hs⟩
  unfold stepG ansOf
  cases u
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hi : i.put
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : w.1 = cur.getD i.key []
      · simp only [h1, ↓reduceIte]
        obtain ⟨S', e, hs⟩ := step_get_cur hS i hi w h1
        exact fin e hs
      · simp only [h1, ↓reduceIte]
        by_cases h2 : w.1 ∈ pend.getD i.key []
        · simp only [h2, ↓reduceIte]
          obtain ⟨S', e, hs⟩ := step_get_pend hc hp hS i hi w h1 h2
          exact fin e hs
        · simp only [h2, ↓reduceIte]
          rw [step_get_no hS i hi w h1 h2]
          exact ⟨rfl, fun _ h => by cases h⟩
    · simp only [↓reduceIte]
      by_cases h1 : w.1 = []
      · simp only [h1, decide_true]
        obtain ⟨S', e, hs⟩ := step_put_ok hc hS i hi w h1
        exact fin e hs
      · simp only [h1, decide_false]
        rw [step_put_no hS i hi w h1]
        exact ⟨rfl, fun _ h => by cases h⟩
  · simp only [↓reduceIte]
    cases hi : i.put
    · simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨S', e, hs⟩ := step_errR hS i hi
      exact fin e hs
    · simp only [↓reduceIte]
      obtain ⟨S', e, hs⟩ := step_errW hp hS i hi
      exact fin e hs

/-- `step`'s next state: two keys, two pending lists, each at most one longer. -/
theorem stepG_lens (cur : List GoString) (pend : List (List GoString)) (i : KIn) (u : Bool)
    (w : GoString) :
    (stepG cur pend i u w).2.1.length = cur.length ∧
      (stepG cur pend i u w).2.2.length = pend.length ∧
      ∀ k, ((stepG cur pend i u w).2.2.getD k []).length ≤ (pend.getD k []).length + 1 := by
  unfold stepG
  refine ⟨?_, ?_, fun k => ?_⟩
  · split <;> (try split) <;> (try split) <;> (try split) <;> simp
  · split <;> (try split) <;> (try split) <;> (try split) <;> simp
  · by_cases hk : i.key = k
    · subst hk
      by_cases hl : i.key < pend.length
      · split <;> (try split) <;> (try split) <;> (try split) <;>
          simp only [getD_set_eq _ _ _ _ hl, List.length_append, List.length_singleton] <;>
          (try have := List.length_erase_le (a := w) (l := pend.getD i.key [])) <;> omega
      · have e : ∀ x : List GoString, (pend.set i.key x).getD i.key [] = pend.getD i.key [] := by
          intro x; simp [List.getD, hl]
        split <;> (try split) <;> (try split) <;> (try split) <;> simp only [e] <;> omega
    · split <;> (try split) <;> (try split) <;> (try split) <;>
        simp only [getD_set_ne _ _ _ hk] <;> omega

/-- The initial set: `initState()`'s. -/
theorem sim_init : Sim [[], []] [[], []] (pInit swB) := by
  refine ⟨fun c hc => ?_, ⟨⟨swB.init, []⟩, rfl, fun k hk => ?_⟩, pInit_closed (P := swB)⟩
  · subst hc
    refine And.intro (fun i hi => by cases hi) (fun k hk => Or.inl ⟨?_, by simp [proj]⟩)
    match k, hk with
    | 0, _ => rfl
    | 1, _ => rfl
  · match k, hk with
    | 0, _ => exact ⟨rfl, by simp [proj]⟩
    | 1, _ => exact ⟨rfl, by simp [proj]⟩

/-! ## The model's state is not a function of kit.go's

Two histories on key 0 from the start, `put(0,"a")` of unknown outcome then `put(0,"b")` answered,
and the same two in the other order, reach the same Go state (`Cur = ["b", ""]`, `Pend = [["a"],
[]]`), but different sets of configurations: only the first allows `"a"` to have taken effect before
`"b"`, leaving `"b"` with nothing pending (in the second, `"a"` is pending after `"b"` and stays
pending, or takes effect). So no representation of the model's states by kit.go's values meets
porcupine's `equalSpec` (`b = true → s = t`) for an `Equal` comparing contents, whatever
its relation to the sets, as long as porcupine's `Step` is specified (`stepSpec`) against
`linkv.pSeq swB` exactly (remote's `PendDec`). -/

/-- `put(0, "a")` and `put(0, "b")`. -/
def putA : KIn := ⟨(true, 0, go!"a"), by decide, by simp⟩
def putB : KIn := ⟨(true, 0, go!"b"), by decide, by simp⟩

/-- The configuration of the first history where `"a"` took effect before `"b"`. -/
def cfgX : PCfg St KIn := ⟨upd swB.init 0 putB.bval, []⟩

theorem reach_nil {c c' : PCfg St KIn} (hr : PReach swB c c') (h : c.pend = []) : c' = c := by
  induction hr with
  | refl => rfl
  | step hs _ ih =>
    cases hs with
    | apply j hj => rw [h] at hj; cases hj
    | perm p hp =>
      rw [h] at hp
      rw [ih (List.Perm.eq_nil hp), List.Perm.eq_nil hp, ← h]

theorem reach_one {σ : St} {c c' : PCfg St KIn} (hr : PReach swB c c')
    (h : c = ⟨σ, [putA]⟩ ∨ c = ⟨upd σ 0 putA.bval, []⟩) :
    c' = ⟨σ, [putA]⟩ ∨ c' = ⟨upd σ 0 putA.bval, []⟩ := by
  induction hr with
  | refl => exact h
  | step hs _ ih =>
    apply ih
    rcases h with rfl | rfl
    · cases hs with
      | apply j hj =>
        have hj' : j = putA := by simpa using hj
        subst hj'
        right
        rw [swB_put putA rfl]
        simp
        rfl
      | perm p hp => left; rw [List.perm_singleton.1 hp]
    · cases hs with
      | apply j hj => cases hj
      | perm p hp => right; rw [List.Perm.eq_nil hp]

/-- **The model's set is not a function of kit.go's state** (see above). -/
theorem equal_unsound :
    stepG [[], []] [[], []] putA true [] = (true, [[], []], [[go!"a"], []]) ∧
    stepG [[], []] [[go!"a"], []] putB false [] = (true, [go!"b", []], [[go!"a"], []]) ∧
    stepG [[], []] [[], []] putB false [] = (true, [go!"b", []], [[], []]) ∧
    stepG [go!"b", []] [[], []] putA true [] = (true, [go!"b", []], [[go!"a"], []]) ∧
    ∃ SA SB : PSet St KIn,
      ((pSeq swB).step (pInit swB) (putA, .err)).bind
          (fun S => (pSeq swB).step S (putB, .ok bnil)) = some SA ∧
      ((pSeq swB).step (pInit swB) (putB, .ok bnil)).bind
          (fun S => (pSeq swB).step S (putA, .err)) = some SB ∧
      SA cfgX ∧ ¬ SB cfgX ∧ SA ≠ SB := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  -- the first history
  obtain ⟨S1, h1, hc1⟩ := pSeq_step_of_pstep (P := swB) (S := pInit swB) (c := ⟨swB.init, []⟩)
    rfl (.errW _ putA rfl rfl) (.single (.apply _ putA (by simp)))
  have e1 : swB.step putB (swB.step putA swB.init).1 = (upd swB.init 0 putB.bval, bnil) := by
    rw [swB_put putB rfl, swB_put putA rfl]
    congr 1
    funext k
    by_cases hk : k = 0 <;> simp [upd, hk, putA, putB]
  have e2 : [putA].erase putA = [] := by simp
  have hok := PStep.ok (P := swB) ⟨(swB.step putA swB.init).1, [putA].erase putA⟩ putB rfl
  simp only [e1, e2] at hok
  have hc1' : S1 ⟨(swB.step putA swB.init).1, []⟩ := by simpa only [e2] using hc1
  obtain ⟨SA, hA, hXA⟩ := pSeq_step_of_pstep hc1' hok (.refl _)
  -- the second
  have hokB := PStep.ok (P := swB) ⟨swB.init, []⟩ putB rfl
  rw [swB_put putB rfl] at hokB
  obtain ⟨S2, h2, hc2⟩ := pSeq_step_of_pstep (P := swB) (S := pInit swB) rfl hokB (.refl _)
  obtain ⟨SB, hB, -⟩ := pSeq_step_of_pstep hc2 (PStep.errW (P := swB) _ putA rfl rfl) (.refl _)
  have hXB : ¬ SB cfgX := by
    rw [pSeq_step_some hB]
    rintro ⟨c0, c, c1, h0, hr, hst, hr'⟩
    rw [pSeq_step_some h2] at h0
    obtain ⟨d0, d, d1, hd0, hdr, hdst, hdr'⟩ := h0
    have hd0' : d0 = ⟨swB.init, []⟩ := hd0
    subst hd0'
    have ed := reach_nil hdr rfl
    subst ed
    obtain ⟨-, ed1⟩ := pstep_ok_inv hdst
    subst ed1
    have ec0 := reach_nil hdr' rfl
    subst ec0
    have ec := reach_nil hr rfl
    subst ec
    rcases pstep_err_inv hst with ⟨-, ec1⟩ | ⟨h, -⟩
    · subst ec1
      rcases reach_one hr' (.inl rfl) with h | h
      · have := congrArg PCfg.pend h
        simp [cfgX] at this
      · have := congrArg (fun c => (c.st 0).1) h
        simp [cfgX, upd, swB, putA, putB, KIn.bval, KIn.val] at this
    · cases h
  refine ⟨SA, SB, by rw [h1]; exact hA, by rw [h2]; exact hB, hXA, hXB, fun e => hXB (e ▸ hXA)⟩

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
