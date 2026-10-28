/-
**S1's invariant, its pure part, and the steps of a sync that keep it** (pure; phase 5 of
`notes/k8s-daemonset-plan.md`). Lean-first.

`s1Ok d σ M L P C` (`S1Inv.lean` holds it with the ghost state):
* `S1` of the API state;
* `acct` (`S1Model.lean`), its pending creates the entries of `P` (pod key and version ↦ the
  create goroutine's permit and node);
* the record of the DaemonSet's owner, if any, for its UID with well-formed versions;
* `claimsOk`: every pod of the DaemonSet on a claimed node is the claimant's pending create.

The steps:
* `create_step`: a create for a claimed node by its claimant (whose permit no entry holds): the
  new pod is pending, S1 kept (`claimsOk` says the node had no other pod of the DaemonSet);
* `wrote_step`: the claimant's `WroteAt` of its pod's version: the entry and the claim go, the
  record covers the pod;
* `noeffect_step`: a call that changed nothing.
There is **no step for an ambiguous create**: the pod was written, the call returned the
timeout, so the goroutine has no version to record and its entry cannot go
(`S1Model.ambiguous_create_breaks_S1`).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Model
public import Proof.k8s_io.kubernetes.pkg.controller.daemon.RvLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open apimodel informer consistency resourceversion

section pure
variable [FfiSyntax]

/-- **The DaemonSet S1 is about**: its owner key (`types.NamespacedName`, the consistency store's
and the work queue's key) and its UID. -/
structure DsId where
  o : Owner
  u : GoString

/-- The pending creates as `acct`'s predicate. -/
def pendOf (P : GMap (Key × Nat) (Nat × GoString)) (k : Key) (c : Nat) : Prop :=
  (P !! (k, c)).isSome

/-- **The claimed nodes are free**: every pod of `u` on a claimed node `n` is pending under the
claimant's permit (an entry of `P` for its key and version, with the permit and `n`). -/
def claimsOk (σ : St) (u : GoString) (C : GMap GoString Nat)
    (P : GMap (Key × Nat) (Nat × GoString)) : Prop :=
  ∀ n i, C !! n = some i → ∀ k o, σ.pods.objs !! k = some o → dsPodOn keyName opIn u n o →
    ∃ c, addedRv σ.pods.log k = some c ∧ P !! (k, c) = some (i, n)

/-- The record, if any, is for `u` and its versions are well formed. -/
def recOk (rc : Option consistency.Rec) (u : GoString) : Prop :=
  ∀ r, rc = some r → r.uid = u ∧ vsWf r.vs

/-- **The pure invariant.** -/
structure s1Ok (d : DsId) (σ : St) (M : GMap Owner consistency.Rec) (L : Nat)
    (P : GMap (Key × Nat) (Nat × GoString)) (C : GMap GoString Nat) : Prop where
  s1 : S1 keyName opIn σ d.u
  acct : acct σ d.u L (M !! d.o) (pendOf P)
  recok : recOk (M !! d.o) d.u
  claims : claimsOk σ d.u C P

/-- A pod of the DaemonSet targets one node. -/
theorem dsPodOn_node_unique {K Op u n n' : GoString} {o : Obj} (h1 : dsPodOn K Op u n' o)
    (h2 : dsPodOn K Op u n o) : n' = n := by
  cases o with
  | pod dd => exact Option.some.inj (h1.2.symm.trans h2.2)
  | _ => exact h1.elim

/-! ### The log's `ADDED` changes -/

theorem addedRv_snoc_added (l : List Change) (c : Change) (k : Key) (hc : c.typ = .added) :
    addedRv (l ++ [c]) k = if c.obj.key = k then some c.rv.toNat else addedRv l k := by
  unfold addedRv
  rw [List.filter_append]
  by_cases hk : c.obj.key = k
  · simp [hc, hk]
  · simp [hk]

/-! ### A create for a claimed node -/

/-- **A create by the claimant of node `n`** (permit `i`, deposited in no entry): the new pod
pending, under `(i, n)`. -/
theorem create_step (d : DsId) (σ : St) (M : GMap Owner consistency.Rec) (L : Nat)
    (P : GMap (Key × Nat) (Nat × GoString)) (C : GMap GoString Nat) (n : GoString) (i : Nat)
    (ns : GoString) (dp : kd.core.Pod) (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time)
    (h : s1Ok d σ M L P C) (hC : C !! n = some i) (hfree : ∀ kc v, P !! kc = some v → v.1 ≠ i)
    (hpod : newPodOk keyName opIn d.u n dp) (herr : createErr .pods ns (.pod dp) σ = none) :
    let o := (createApply .pods ns (.pod dp) σ t).1
    let σ' := (createApply .pods ns (.pod dp) σ t).2
    s1Ok d σ' M L (<[(o.key, (σ.rev + 1).toNat) := (i, n)]> P) C ∧
      addedRv σ'.pods.log o.key = some (σ.rev + 1).toNat ∧
      o.meta.ResourceVersion' = rvStr (σ.rev + 1) := by
  intro o σ'
  obtain ⟨hk, hon⟩ := createApply_pod keyName opIn d.u n ns dp σ t hpod
  -- the new pod's key is fresh
  have hfresh : σ.pods.objs !! o.key = none := by
    rw [hk]
    cases hl : σ.pods.objs !! mkKey ns (dp.ObjectMeta'.GenerateName' ++ rvStr (σ.rev + 1)) with
    | none => rfl
    | some x =>
      exfalso
      simp [createErr, createNs, Res.namespaced, Obj.modMeta, Obj.setMeta, Obj.meta, hpod.noRv, hpod.noName, hpod.noNs, hpod.gen, St.tbl] at herr
      have e : σ.rev + 1 = σ.rev + 1#64 := rfl
      rw [e] at hl
      rw [hl] at herr
      cases herr

  have hobjs : σ'.pods.objs = <[o.key := o]> σ.pods.objs := by
    simp [σ', o, createApply, St.setTbl, St.tbl]
  have hlog : σ'.pods.log = σ.pods.log ++ [⟨.added, σ.rev + 1, o⟩] := by
    simp [σ', o, createApply, St.setTbl, St.tbl]
  have hrv : o.meta.ResourceVersion' = rvStr (σ.rev + 1) := by
    simp [o, createApply, Obj.modMeta, Obj.setMeta, Obj.meta_setMeta, Obj.meta, prepareD, createNs,
      Res.namespaced, preparePodD, hpod.noNs]
  have hadd : ∀ k, addedRv σ'.pods.log k =
      if o.key = k then some (σ.rev + 1).toNat else addedRv σ.pods.log k := by
    intro k; rw [hlog]; exact addedRv_snoc_added _ _ k rfl
  -- no pod of `u` on `n` before: the claim's pods are pending under `i`, and no entry is
  have hnone : ∀ k o', σ.pods.objs !! k = some o' → ¬ dsPodOn keyName opIn d.u n o' := by
    intro k o' hk' hd
    obtain ⟨c, -, hP⟩ := h.claims n i hC k o' hk' hd
    exact hfree _ _ hP rfl
  refine ⟨⟨?_, ?_, h.recok, ?_⟩, by rw [hadd]; simp, hrv⟩
  · -- S1
    intro k1 k2 o1 o2 n' h1 h2 hd1 hd2
    rw [hobjs] at h1 h2
    simp only [GMap.lookup_insert_eq_iff] at h1 h2
    by_cases e1 : o.key = k1 <;> by_cases e2 : o.key = k2
    · exact e1.symm.trans e2
    · simp only [e1, ↓reduceIte, Option.some.injEq] at h1
      simp only [e2, ↓reduceIte] at h2
      subst h1
      have : n' = n := dsPodOn_node_unique hd1 hon
      subst this
      exact absurd hd2 (hnone k2 o2 h2)
    · simp only [e2, ↓reduceIte, Option.some.injEq] at h2
      simp only [e1, ↓reduceIte] at h1
      subst h2
      have : n' = n := dsPodOn_node_unique hd2 hon
      subst this
      exact absurd hd1 (hnone k1 o1 h1)
    · simp only [e1, e2, ↓reduceIte] at h1 h2
      exact h.s1 k1 k2 o1 o2 n' h1 h2 hd1 hd2
  · -- acct
    intro k o' hk' hu
    rw [hobjs] at hk'
    simp only [GMap.lookup_insert_eq_iff] at hk'
    by_cases e : o.key = k
    · subst e
      refine ⟨(σ.rev + 1).toNat, by rw [hadd]; simp, Or.inr (Or.inr ?_)⟩
      simp [pendOf]
    · simp only [e, ↓reduceIte] at hk'
      obtain ⟨c, hc, hcase⟩ := h.acct k o' hk' hu
      refine ⟨c, by rw [hadd, if_neg e]; exact hc, ?_⟩
      rcases hcase with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · refine Or.inr (Or.inr ?_)
        unfold pendOf at h3 ⊢
        rw [GMap.lookup_insert_ne _ _ (by intro he; exact e (congrArg Prod.fst he))]
        exact h3
  · -- the claims
    intro n' i' hC' k o' hk' hd
    rw [hobjs] at hk'
    simp only [GMap.lookup_insert_eq_iff] at hk'
    by_cases e : o.key = k
    · subst e
      simp only [↓reduceIte, Option.some.injEq] at hk'
      subst hk'
      have : n' = n := dsPodOn_node_unique hd hon
      subst this
      rw [hC] at hC'
      cases hC'
      exact ⟨(σ.rev + 1).toNat, by rw [hadd]; simp, by simp⟩
    · simp only [e, ↓reduceIte] at hk'
      obtain ⟨c, hc, hP⟩ := h.claims n' i' hC' k o' hk' hd
      refine ⟨c, by rw [hadd, if_neg e]; exact hc, ?_⟩
      rw [GMap.lookup_insert_ne _ _ (by intro he; exact e (congrArg Prod.fst he))]
      exact hP

/-! ### The claimant's `WroteAt` -/

/-- **The claimant's `WroteAt`** of its pod's version `rvStr c`, for the DaemonSet's owner and
UID: the entry and the claim go; the record covers the pod. -/
theorem wrote_step (d : DsId) (σ : St) (M : GMap Owner consistency.Rec) (L : Nat)
    (P : GMap (Key × Nat) (Nat × GoString)) (C : GMap GoString Nat) (n : GoString) (i : Nat)
    (k : Key) (c : w64) (h : s1Ok d σ M L P C) (hP : P !! (k, c.toNat) = some (i, n))
    (hc : 1 ≤ c.toNat) :
    s1Ok d σ (wroteAtM M d.o d.u podGR (rvStr c)) L (GMap.delete (k, c.toNat) P)
      (GMap.delete n C) := by
  have hwf : vsWf (recFor M d.o d.u).vs := by
    unfold recFor
    split
    · rename_i r hr
      split
      · exact (h.recok r hr).2
      · intro gr x hx; simp at hx
    · intro gr x hx; simp at hx
  have huid : ∀ r, M !! d.o = some r → r.uid = d.u := fun r hr => (h.recok r hr).1
  refine ⟨h.s1, ?_, ?_, ?_⟩
  · intro k' o' hk' hu
    obtain ⟨c', hc', hcase⟩ := h.acct k' o' hk' hu
    refine ⟨c', hc', ?_⟩
    by_cases e : (k', c') = (k, c.toNat)
    · -- the written pod: covered by the record now
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      refine Or.inr (Or.inl ?_)
      exact recCovers_wroteAt_new M d.o d.u (rvStr c) _ hwf (wellFormed_rvStr c hc)
        (by rw [decVal_rvStr]; exact Nat.le_refl _)
    · rcases hcase with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr (Or.inl (recCovers_wroteAt M d.o d.u podGR (rvStr c) c' huid h2))
      · refine Or.inr (Or.inr ?_)
        unfold pendOf at h3 ⊢
        rw [GMap.lookup_delete_ne _ (Ne.symm e)]
        exact h3
  · -- the record: for `u`, well formed
    intro r hr
    unfold wroteAtM at hr
    simp only [GMap.lookup_insert_eq, Option.some.injEq] at hr
    subst hr
    refine ⟨rfl, wroteAtVs_wf _ _ _ hwf⟩
  · intro n' i' hC' k' o' hk' hd
    have hn : n' ≠ n := by
      intro e; subst e; simp at hC'
    rw [GMap.lookup_delete_ne _ (Ne.symm hn)] at hC'
    obtain ⟨c', hc', hP'⟩ := h.claims n' i' hC' k' o' hk' hd
    refine ⟨c', hc', ?_⟩
    have hne : (k', c') ≠ (k, c.toNat) := by
      intro e
      rw [e, hP] at hP'
      cases hP'
      exact hn rfl
    rw [GMap.lookup_delete_ne _ (Ne.symm hne)]
    exact hP'

end pure

end dsctl
end EtcdGrove
end Perennial
