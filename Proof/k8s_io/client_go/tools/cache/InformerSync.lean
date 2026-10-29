/-
**The FIFO's initial population and the first relist** (phase 4 of `notes/k8s-daemonset-plan.md`,
fifth round): the pure part of the informer invariant that makes `HasSynced` mean "the first list is
in the store". Lean-first.

The FIFO (`the_real_fifo.go`) counts the initial items: its first `Replace` sets
`initialPopulationCount` to the queue's length (the relist's delta the last of them), each `Pop`'s
deferred step lowers it by the deltas it processed, and the queue is synced once it is `0`
(`FQ.replace`, `FQ.popDoneN`). The informer's reflector pushes nothing before its first list, so
the queue is empty and nothing is popped until then (`syncOk`'s first half), and the count is the
position, among the deltas not yet done, of the first relist (`syncOk`'s second half: the relist's
delta is the `initCount`-th of the popped-but-not-applied and the queued ones, after the
`apN` applied ones, or the store is already at its version). So once synced, the store's version
is at least the first list's (`syncOk`'s `synced` clause).

`f` is the first list's version (`none` before it), which the invariant keeps in a ghost variable
(persistent once set: `infFirst`).
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerRel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informer

open apimodel cache

section sync
variable [GooseExts] [GoGlobalContext]

/-- The popped deltas already applied to the store and not yet done (`Pop`'s deferred step). -/
def apN (pd : List cache.FD) (ap : Bool) : Nat := if ap then pd.length else 0

/-- **The initial population's relation** (see the file header). -/
def syncOk (q : cache.FQ) (pd : List cache.FD) (ap : Bool) (s : InfP) (f : Option Nat) : Prop :=
  (q.populated = false →
    pd = [] ∧ q.items = [] ∧ s.last = none ∧ q.initCount = 0 ∧ q.synced = false ∧ f = none) ∧
  (q.populated = true → ∃ v, f = some v ∧ s.last ≠ none ∧
    (q.synced = false → 0 < q.initCount) ∧ (q.synced = true → v ≤ rvNat s.store.rv) ∧
    (v ≤ rvNat s.store.rv ∨ (apN pd ap < q.initCount ∧
      ∃ M, (s.popped ++ s.fifo)[q.initCount - 1 - apN pd ap]? = some (.replaced M v))))

/-- **A relist applied**: the store's version is at least its version after the deltas through it. -/
theorem replaced_applied (l : List Change) (hs : l.Pairwise (fun a b => a.rv.toNat < b.rv.toNat)) :
    ∀ (st : View) (ds rest : List Delta) (w : Option Nat) (M : GMap Key Obj) (v : Nat),
      Inf.ok l ⟨st, ds ++ rest, w⟩ → Delta.replaced M v ∈ ds → v ≤ rvNat (st.applyAll ds).rv
  | _, [], _, _, _, _, _, hm => by simp at hm
  | st, d :: ds, rest, w, M, v, h, hm => by
    have h' := ok_pop l hs st d _ w h
    rcases List.mem_cons.1 hm with he | hm
    · subst he
      have := rvNat_mono (applyAll_rv_le l hs (st.apply (.replaced M v)) ds rest w h')
      exact this
    · exact replaced_applied l hs (st.apply d) ds rest w M v h' hm

/-- **A pop** (`PopBatch`'s first linearization point) keeps the relation. -/
theorem sync_pop (q : cache.FQ) (s : InfP) (f : Option Nat) (m1 m2 : List Delta)
    (items' pd' : List cache.FD) (h : syncOk q [] false s f) (hp0 : s.popped = [])
    (hf : s.fifo = m1 ++ m2) (hne : q.items ≠ []) :
    syncOk { q with items := items' } pd' false ⟨s.store, m1, m2, s.last⟩ f := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hp => absurd (h1 hp).2.1 hne, fun hp => ?_⟩
  obtain ⟨v, hv, hl, hsy, hsy2, hd⟩ := h2 hp
  refine ⟨v, hv, hl, hsy, hsy2, ?_⟩
  simp only [apN, Bool.false_eq_true, ↓reduceIte] at hd ⊢
  rw [hp0, hf, List.nil_append] at hd
  exact hd

/-- **The store applies the popped deltas** (a writer's step or a processing's finish). -/
theorem sync_apply (l : List Change) (hs : l.Pairwise (fun a b => a.rv.toNat < b.rv.toNat))
    (q : cache.FQ) (pd : List cache.FD) (s : InfP) (f : Option Nat) (h : syncOk q pd false s f)
    (hlen : pd.length = s.popped.length) (hok : s.ok l) :
    syncOk q pd true ⟨s.store.applyAll s.popped, [], s.fifo, s.last⟩ f := by
  obtain ⟨h1, h2⟩ := h
  have hmono := rvNat_mono (InfP.apply_rv_le l hs s hok)
  refine ⟨fun hp => h1 hp, fun hp => ?_⟩
  obtain ⟨v, hv, hl, hsy, hsy2, hd⟩ := h2 hp
  refine ⟨v, hv, hl, hsy, fun h => Nat.le_trans (hsy2 h) hmono, ?_⟩
  simp only [apN, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] at hd ⊢
  rcases hd with hd | ⟨hlt, M, hM⟩
  · exact Or.inl (Nat.le_trans hd hmono)
  · by_cases hi : q.initCount - 1 < s.popped.length
    · left
      rw [List.getElem?_append_left hi] at hM
      exact replaced_applied l hs s.store s.popped s.fifo s.last M v hok (List.mem_of_getElem? hM)
    · right
      refine ⟨by omega, M, ?_⟩
      rw [List.getElem?_append_right (by omega)] at hM
      rw [List.nil_append, hlen]
      exact hM

/-- **`PopBatch`'s deferred step**: the applied deltas are done, the count lowered by them. -/
theorem sync_done (q : cache.FQ) (pd : List cache.FD) (s : InfP) (f : Option Nat)
    (h : syncOk q pd true s f) (hp0 : s.popped = []) :
    syncOk (q.popDoneN pd.length) [] false s f := by
  obtain ⟨h1, h2⟩ := h
  unfold cache.FQ.popDoneN
  split
  · rename_i hpos
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · have := (h1 hp).2.2.2.1; omega
    · obtain ⟨v, hv, hl, hsy, hsy2, hd⟩ := h2 hp
      simp only at hp
      simp only [apN, ↓reduceIte] at hd
      refine ⟨v, hv, hl, ?_, ?_, ?_⟩
      · intro hs'
        simp only [hp, Bool.true_and, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hs'
        show 0 < q.initCount - pd.length
        omega
      · intro hs'
        simp only [hp, Bool.true_and, Bool.or_eq_true, beq_iff_eq] at hs'
        rcases hs' with hs' | hs'
        · exact hsy2 hs'
        · rcases hd with hd | ⟨hlt, -⟩
          · exact hd
          · omega
      · rcases hd with hd | ⟨hlt, M, hM⟩
        · exact Or.inl hd
        · right
          simp only [apN, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero]
          refine ⟨by omega, M, ?_⟩
          rw [hp0] at hM ⊢
          rw [show q.initCount - pd.length - 1 = q.initCount - 1 - pd.length by omega]
          exact hM
  · rename_i hpos
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · obtain ⟨-, h1'⟩ := h1 hp
      exact ⟨rfl, h1'⟩
    · obtain ⟨v, hv, hl, hsy, hsy2, hd⟩ := h2 hp
      have hsyt : q.synced = true := by
        cases hq : q.synced with
        | true => rfl
        | false => have := hsy hq; omega
      exact ⟨v, hv, hl, hsy, hsy2, Or.inl (hsy2 hsyt)⟩

/-- **A delta pushed to a populated queue** (a change, a bookmark, a later relist), the count and
the flag kept. -/
theorem sync_push (q q' : cache.FQ) (pd : List cache.FD) (ap : Bool) (s : InfP) (f : Option Nat)
    (d : Delta) (w : Nat) (h : syncOk q pd ap s f) (hq : q.populated = true)
    (hp' : q'.populated = true) (hi : q'.initCount = q.initCount) (hsy : q'.synced = q.synced) :
    syncOk q' pd ap ⟨s.store, s.popped, s.fifo ++ [d], some w⟩ f := by
  refine ⟨fun h' => (by rw [hp'] at h'; cases h'), fun _ => ?_⟩
  obtain ⟨v, hv, -, hs1, hs2, hd⟩ := h.2 hq
  refine ⟨v, hv, by simp, by rw [hsy, hi]; exact hs1, by rw [hsy]; exact hs2, ?_⟩
  rw [hi]
  rcases hd with hd | ⟨hlt, M, hM⟩
  · exact Or.inl hd
  · right
    refine ⟨hlt, M, ?_⟩
    have hb := (List.getElem?_eq_some_iff.1 hM).1
    rw [← List.append_assoc, List.getElem?_append_left hb]
    exact hM

/-- A populated queue's `Add`/`Update`/`Delete` keeps its synced flag (a count of `0` means it is
already synced). -/
theorem sync_addObj_synced (q : cache.FQ) (pd : List cache.FD) (ap : Bool) (s : InfP)
    (f : Option Nat) (t : GoString) (x : GoInterface) (h : syncOk q pd ap s f)
    (hq : q.populated = true) : (q.addObj t x).synced = q.synced := by
  obtain ⟨v, -, -, hs1, -⟩ := h.2 hq
  unfold cache.FQ.addObj
  cases hs : q.synced with
  | true => rfl
  | false =>
    have := hs1 hs
    simp only [Bool.false_or, beq_eq_false_iff_ne]
    omega

/-- A queue with a last version (the reflector listed) is populated. -/
theorem sync_populated (q : cache.FQ) (pd : List cache.FD) (ap : Bool) (s : InfP)
    (f : Option Nat) (h : syncOk q pd ap s f) (u : Nat) (hu : s.last = some u) :
    q.populated = true := by
  cases hp : q.populated with
  | true => rfl
  | false => have := (h.1 hp).2.2.1; rw [hu] at this; cases this

/-- **The first relist**: the queue, empty, holds the relist, the count `1`; its version the first
list's. -/
theorem sync_replace_first (q : cache.FQ) (pd : List cache.FD) (ap : Bool) (s : InfP)
    (f : Option Nat) (xs : List GoInterface) (rvs : GoString) (M : GMap Key Obj) (w : Nat)
    (h : syncOk q pd ap s f) (hq : q.populated = false) (hfifo0 : s.fifo = [])
    (hpop0 : s.popped = []) :
    syncOk (q.replace xs rvs) pd ap ⟨s.store, s.popped, s.fifo ++ [.replaced M w], some w⟩
      (some w) := by
  obtain ⟨hpd, hit, -, hic, hsy, -⟩ := h.1 hq
  unfold cache.FQ.replace
  rw [hq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine ⟨fun h' => (by cases h'), fun _ => ⟨w, rfl, by simp, fun _ => by simp, ?_, ?_⟩⟩
  · intro h'; rw [hsy] at h'; cases h'
  · right
    subst hpd
    simp [apN, hit, hfifo0, hpop0]

end sync

end informer
end EtcdGrove
end Perennial
