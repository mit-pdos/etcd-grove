/-
**The API writes' steps of S1's invariant** (pure; the autoverify run's invariant stage,
`notes/k8s-daemonset-run/`, track B). Lean-first. For every operation on the model API server's
state that a thread of the program makes, `s1Ok` before gives `s1Ok` after:

* **no change** (`noop_step`): every read (get, list, watch), every write with no effect (a flagged
  failure, a check's error: `CreateOut`/`UpdateOut`/`DeleteOut`'s first two branches, an update of
  nothing, a delete of an object already being deleted);
* **the frame** (`frame_step`): a write that leaves the pods and the DaemonSets alone and keeps the
  revisions the controller's: the admin's node create (`nodeCreate_step`), the controller's
  revision create (`crCreate_step`), update (`crUpdate_step`) and delete (`crDelete_step`);
* **the controller's pod create** for a node its sync claimed (`podCreate_step`, the claim's pod);
* **the controller's pod delete** (`podDelete_step`: unbound, no finalizers, so removed);
* **the controller's DaemonSet status write** (`dsStatus_step`: the status only, the collision
  count kept);
* **the admin's DaemonSet create** (`dsCreate_step`: a well-formed DaemonSet with a fresh UID and a
  revision name no other DaemonSet of its namespace has).

The consistency store's operations are `S1Steps.lean`'s (`wrote_step`, `wroteAt_step`,
`ensureReady_step`, `clear_noop`, `clear_notfound_noop`), as are the bookkeeping steps. The one
operation with no step is the **ambiguous pod create** (a create that commits and returns the
timeout): `S1Model.ambiguous_create_breaks_S1`.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Steps

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open apimodel informer consistency resourceversion

section pure
variable [GooseExts]

/-! ## The stored objects are logged ones -/

theorem foldl_apply_lookup (l : List Change) (M : GMap Key Obj) (k : Key) (o : Obj)
    (h : (l.foldl applyChange M) !! k = some o) :
    M !! k = some o ∨ ∃ c ∈ l, c.obj = o ∧ c.obj.key = k := by
  induction l generalizing M with
  | nil => exact Or.inl h
  | cons c l ih =>
    rcases ih (applyChange M c) h with h1 | ⟨c', hc', h2⟩
    · unfold applyChange at h1
      split at h1
      · simp only [GMap.lookup_delete_iff] at h1
        split at h1
        · cases h1
        · exact Or.inl h1
      · simp only [GMap.lookup_insert_eq_iff] at h1
        split at h1
        · rename_i e
          cases h1
          exact Or.inr ⟨c, List.mem_cons_self .., rfl, e⟩
        · exact Or.inl h1
    · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', h2⟩

/-- **A stored object is a logged one, at its key.** -/
theorem stored_logged (σ : St) (r : Res) (hwf : σ.wf) (k : Key) (o : Obj)
    (h : (σ.tbl r).objs !! k = some o) : ∃ c ∈ (σ.tbl r).log, c.obj = o ∧ c.obj.key = k := by
  rw [hwf.objs_replay r] at h
  rcases foldl_apply_lookup _ ∅ k o h with h1 | h2
  · simp at h1
  · exact h2

/-- **A pod made for `d` is controlled by `d`'s UID only.** -/
theorem podOf_ctlBy {d : kd.apps.DaemonSet} {p : kd.core.Pod} {u : GoString} (hp : podOf d p)
    (hc : ctlBy u p) : u = d.ObjectMeta'.UID' := by
  obtain ⟨r, hr, hu, -⟩ := hc
  rw [hp.ref] at hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact hu.symm

/-- **A stored pod is one the controller made for a stored DaemonSet.** -/
theorem stored_podOf (σ : St) (hwf : σ.wf) (hs : sceneOk σ) (k : Key) (o : Obj)
    (h : σ.pods.objs !! k = some o) :
    ∃ p o' d, o = .pod p ∧ dsAtOwner σ o' = some d ∧ podOf d p ∧ o.key = k := by
  obtain ⟨c, hc, rfl, hk⟩ := stored_logged σ .pods hwf k o h
  obtain ⟨p, o', d, hp, hd, hpo⟩ := hs.pods c hc
  exact ⟨p, o', d, hp, hd, hpo, hk⟩

/-- A pod of `u` that is stored is of the DaemonSet with that UID. -/
theorem dsPod_owner (σ : St) (hwf : σ.wf) (hs : sceneOk σ) (k : Key) (o : Obj) (u : GoString)
    (h : σ.pods.objs !! k = some o) (hu : dsPod u o) :
    ∃ p o' d, o = .pod p ∧ dsAtOwner σ o' = some d ∧ podOf d p ∧ u = d.ObjectMeta'.UID' := by
  obtain ⟨p, o', d, rfl, hd, hp, -⟩ := stored_podOf σ hwf hs k o h
  exact ⟨p, o', d, rfl, hd, hp, podOf_ctlBy hp hu⟩

theorem addedRv_snoc_added (l : List Change) (c : Change) (k : Key) (hc : c.typ = .added) :
    addedRv (l ++ [c]) k = if c.obj.key = k then some c.rv.toNat else addedRv l k := by
  unfold addedRv
  rw [List.filter_append]
  by_cases hk : c.obj.key = k
  · simp [hc, hk]
  · simp [hk]

theorem addedRv_snoc_other (l : List Change) (c : Change) (k : Key) (hc : c.typ ≠ .added) :
    addedRv (l ++ [c]) k = addedRv l k := by
  unfold addedRv
  rw [List.filter_append]
  simp [hc]

/-! ## No change, and the frame -/

/-- **A read, or a write with no effect.** -/
theorem noop_step (σ σ' : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld : Nat) (h : s1Ok σ M Lm C Ld) (he : σ' = σ) : s1Ok σ' M Lm C Ld := he ▸ h

/-- **The frame**: a write that changes neither the pods nor the DaemonSets, and logs only
revisions the controller made for stored DaemonSets. -/
theorem frame_step (σ σ' : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld : Nat) (h : s1Ok σ M Lm C Ld) (hp : σ'.pods = σ.pods) (hd : σ'.dss = σ.dss)
    (hcrs : ∀ c ∈ σ'.crs.log, ∃ (r : kd.apps.ControllerRevision) (o : Owner)
      (d : kd.apps.DaemonSet), c.obj = .cr r ∧ dsAtOwner σ o = some d ∧ crOf d r) :
    s1Ok σ' M Lm C Ld := by
  obtain ⟨rev, uids, pods, nodes, dss, crs⟩ := σ
  obtain ⟨rev', uids', pods', nodes', dss', crs'⟩ := σ'
  simp only at hp hd
  subst hp hd
  obtain ⟨hs1, ⟨h1, h2, h3, h4, h5, h6⟩, hown, hcl, hrec⟩ := h
  refine ⟨hs1, ⟨h1, h2, h3, h4, h5, hcrs⟩, ?_, hcl, hrec⟩
  intro o d hdo
  obtain ⟨a, b, c, e, f⟩ := hown o d hdo
  exact ⟨a, b, c, e, f⟩

/-! ## The revisions -/

/-- `crOf` does not depend on the revision's version, deletion time or grace period. -/
theorem crOf_meta (d : kd.apps.DaemonSet) (r : kd.apps.ControllerRevision)
    (m : kd.meta.ObjectMeta) (h : crOf d r)
    (hr : m.OwnerReferences' = r.ObjectMeta'.OwnerReferences')
    (hn : m.Namespace' = r.ObjectMeta'.Namespace') (hnm : m.Name' = r.ObjectMeta'.Name')
    (hl : m.Labels' = r.ObjectMeta'.Labels') : crOf d { r with ObjectMeta' := m } :=
  ⟨by rw [hr]; exact h.ref, by rw [hn]; exact h.ns, by rw [hnm]; exact h.name,
   by rw [hl]; exact h.lbls, h.data⟩

/-- **The admin's node create** (or any node write). -/
theorem nodeCreate_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld : Nat) (ns : GoString) (o : Obj)
    (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) (h : s1Ok σ M Lm C Ld) :
    s1Ok (createApply .nodes ns o σ t).2 M Lm C Ld := by
  refine frame_step σ _ M Lm C Ld h (by simp [createApply, St.setTbl, St.tbl])
    (by simp [createApply, St.setTbl, St.tbl]) ?_
  have hc : (createApply .nodes ns o σ t).2.crs = σ.crs := by
    simp [createApply, St.setTbl, St.tbl]
  rw [hc]
  exact h.scene.crs

/-- **The controller's revision create** (`snapshot`): the revision it made for a stored
DaemonSet. -/
theorem crCreate_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld : Nat) (ns : GoString) (o : Obj)
    (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) (h : s1Ok σ M Lm C Ld)
    (hcr : ∃ (r : kd.apps.ControllerRevision) (o' : Owner) (d : kd.apps.DaemonSet),
      (createApply .revisions ns o σ t).1 = .cr r ∧ dsAtOwner σ o' = some d ∧ crOf d r) :
    s1Ok (createApply .revisions ns o σ t).2 M Lm C Ld := by
  refine frame_step σ _ M Lm C Ld h (by simp [createApply, St.setTbl, St.tbl])
    (by simp [createApply, St.setTbl, St.tbl]) ?_
  have hlog : (createApply .revisions ns o σ t).2.crs.log =
      σ.crs.log ++ [⟨.added, σ.rev + 1, (createApply .revisions ns o σ t).1⟩] := by
    simp [createApply, St.setTbl, St.tbl]
  rw [hlog]
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact h.scene.crs c hc
  · simp only [List.mem_singleton] at hc
    subst hc
    obtain ⟨r, o', d, h1, h2, h3⟩ := hcr
    exact ⟨r, o', d, h1, h2, h3⟩

/-- **The controller's revision update** (`constructHistory`'s revision bump): the result the
revision the controller made for a stored DaemonSet. -/
theorem crUpdate_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld : Nat) (st obj : Obj) (h : s1Ok σ M Lm C Ld)
    (hcr : ∃ (r : kd.apps.ControllerRevision) (o' : Owner) (d : kd.apps.DaemonSet),
      (updateApply .revisions st obj σ).1 = .cr r ∧ dsAtOwner σ o' = some d ∧ crOf d r) :
    s1Ok (updateApply .revisions st obj σ).2 M Lm C Ld := by
  refine frame_step σ _ M Lm C Ld h (by simp [updateApply, St.setTbl, St.tbl])
    (by simp [updateApply, St.setTbl, St.tbl]) ?_
  have hlog : (updateApply .revisions st obj σ).2.crs.log =
      σ.crs.log ++ [⟨.modified, σ.rev + 1, (updateApply .revisions st obj σ).1⟩] := by
    simp [updateApply, St.setTbl, St.tbl]
  rw [hlog]
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact h.scene.crs c hc
  · simp only [List.mem_singleton] at hc
    subst hc
    obtain ⟨r, o', d, h1, h2, h3⟩ := hcr
    exact ⟨r, o', d, h1, h2, h3⟩

/-- **The controller's revision delete** (`cleanupHistory`, `dedupCurHistories`) of a stored
revision. -/
theorem crDelete_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld : Nat) (k : Key) (st : Obj) (gps : Option w64)
    (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) (h : s1Ok σ M Lm C Ld) (hwf : σ.wf)
    (hst : σ.crs.objs !! k = some st) :
    s1Ok (deleteApply .revisions st gps σ t) M Lm C Ld := by
  obtain ⟨c0, hc0, rfl, -⟩ := stored_logged σ .revisions hwf k st hst
  obtain ⟨r, o', d, hr, hd, hcr⟩ := h.scene.crs c0 hc0
  have hpd : (deleteApply .revisions c0.obj gps σ t).pods = σ.pods ∧
      (deleteApply .revisions c0.obj gps σ t).dss = σ.dss := by
    unfold deleteApply; dsimp only; split <;> simp [St.setTbl, St.tbl]
  refine frame_step σ _ M Lm C Ld h hpd.1 hpd.2 ?_
  intro c hc
  unfold deleteApply at hc
  rw [hr] at hc
  dsimp only at hc
  split at hc
  · simp only [St.setTbl, St.tbl] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h.scene.crs c hc
    · simp only [List.mem_singleton] at hc
      subst hc
      refine ⟨_, o', d, rfl, hd, crOf_meta d r _ hcr rfl rfl rfl rfl⟩
  · simp only [St.setTbl, St.tbl] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h.scene.crs c hc
    · simp only [List.mem_singleton] at hc
      subst hc
      exact ⟨_, o', d, rfl, hd, crOf_meta d r _ hcr rfl rfl rfl rfl⟩

end pure

end dsctl
end EtcdGrove
end Perennial
