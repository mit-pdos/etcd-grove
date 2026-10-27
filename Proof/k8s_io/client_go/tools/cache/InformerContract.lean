/-
**The informer contract with a popped batch** (phase 4 of `notes/k8s-daemonset-plan.md`, fourth
round): `InformerModel.lean`'s pure contract extended with the deltas popped from the FIFO and not
yet applied to the store (`PopBatch`'s first linearization point removes a batch from the queue; the
store applies it later, in one transaction on the batch path, `Transaction`, or one delta at a
time). Lean-first.

The invariant (`InfP.ok`) is `Inf.ok` of the store and the popped deltas followed by the queue:
popping moves deltas from the queue to the popped ones without changing the chain
(`InfP.ok_pop`); applying them is `Inf.ok`'s pops in sequence (`InfP.ok_apply`), the store's version
never decreasing (`applyAll_rv_le`).
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informer

open apimodel

section model
variable [FfiSyntax]

/-- The store after applying deltas in order. -/
def View.applyAll (s : View) (ds : List Delta) : View := ds.foldl View.apply s

theorem rvLe_trans {a b c : Option Nat} (h1 : rvLe a b) (h2 : rvLe b c) : rvLe a c := by
  cases a with
  | none => trivial
  | some a =>
    cases b with
    | none => exact absurd h1 id
    | some b =>
      cases c with
      | none => exact absurd h2 id
      | some c => simp only [rvLe] at h1 h2 ⊢; omega

theorem rvLe_refl (a : Option Nat) : rvLe a a := by cases a <;> simp [rvLe]

/-- **Applying deltas in order keeps the invariant.** -/
theorem ok_applyAll (l : List Change) (hs : l.Pairwise (fun a b => a.rv.toNat < b.rv.toNat)) :
    ∀ (st : View) (ds rest : List Delta) (w : Option Nat),
      Inf.ok l ⟨st, ds ++ rest, w⟩ → Inf.ok l ⟨st.applyAll ds, rest, w⟩
  | _, [], _, _, h => h
  | st, d :: ds, rest, w, h => ok_applyAll l hs (st.apply d) ds rest w (ok_pop l hs st d _ w h)

/-- **The store's version never decreases** when it applies deltas in order. -/
theorem applyAll_rv_le (l : List Change) (hs : l.Pairwise (fun a b => a.rv.toNat < b.rv.toNat)) :
    ∀ (st : View) (ds rest : List Delta) (w : Option Nat),
      Inf.ok l ⟨st, ds ++ rest, w⟩ → rvLe st.rv (st.applyAll ds).rv
  | _, [], _, _, _ => rvLe_refl _
  | st, d :: ds, rest, w, h =>
    rvLe_trans (pop_rv_le l st d _ w h)
      (applyAll_rv_le l hs (st.apply d) ds rest w (ok_pop l hs st d _ w h))

/-- **An informer's abstract state, with the popped deltas**: the store, the deltas popped and not
yet applied, the queue, the reflector's last version. -/
structure InfP where
  store : View
  popped : List Delta
  fifo : List Delta
  last : Option Nat

/-- **The invariant**: the store and the popped deltas, then the queue, are a chain. -/
def InfP.ok (l : List Change) (s : InfP) : Prop := Inf.ok l ⟨s.store, s.popped ++ s.fifo, s.last⟩

/-- **A pop**: deltas move from the queue to the popped ones. -/
theorem InfP.ok_pop (l : List Change) (s : InfP) (ds : List Delta) (rest : List Delta)
    (hf : s.fifo = ds ++ rest) (h : s.ok l) :
    InfP.ok l ⟨s.store, s.popped ++ ds, rest, s.last⟩ := by
  unfold InfP.ok at h ⊢
  rw [hf, ← List.append_assoc] at h
  exact h

/-- **The store applies the popped deltas.** -/
theorem InfP.ok_apply (l : List Change) (hs : l.Pairwise (fun a b => a.rv.toNat < b.rv.toNat))
    (s : InfP) (h : s.ok l) : InfP.ok l ⟨s.store.applyAll s.popped, [], s.fifo, s.last⟩ := by
  unfold InfP.ok at h ⊢
  exact ok_applyAll l hs s.store s.popped s.fifo s.last h

/-- The store's version does not decrease when it applies the popped deltas. -/
theorem InfP.apply_rv_le (l : List Change) (hs : l.Pairwise (fun a b => a.rv.toNat < b.rv.toNat))
    (s : InfP) (h : s.ok l) : rvLe s.store.rv (s.store.applyAll s.popped).rv :=
  applyAll_rv_le l hs s.store s.popped s.fifo s.last h

/-- **The reflector enqueues** (as `Inf`'s `ok_push_*`): the queue grows at its end. -/
theorem InfP.ok_push (l : List Change) (s : InfP) (d : Delta) (w : Option Nat)
    (h : Inf.ok l ⟨s.store, s.popped ++ s.fifo ++ [d], w⟩) :
    InfP.ok l ⟨s.store, s.popped, s.fifo ++ [d], w⟩ := by
  unfold InfP.ok; rw [← List.append_assoc]; exact h

/-- **The server's log grows** after the versions the informer has. -/
theorem InfP.ok_extend (l l' : List Change) (s : InfP) (b : Nat) (h : s.ok l)
    (hw : rvLe s.last (some b)) (hl' : ∀ c ∈ l', b < c.rv.toNat) : s.ok (l ++ l') :=
  informer.ok_extend l l' ⟨s.store, s.popped ++ s.fifo, s.last⟩ b h hw hl'

/-- The store's contents at its version. -/
theorem InfP.ok_store (l : List Change) (s : InfP) (u : Nat) (h : s.ok l)
    (hu : s.store.rv = some u) : s.store.items = tableAt l u :=
  informer.ok_store l ⟨s.store, s.popped ++ s.fifo, s.last⟩ u h hu

end model

end informer
end EtcdGrove
end Perennial
