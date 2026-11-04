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

/-! ## Congruences -/

theorem S1_pods (σ σ' : St) (u : GoString) (hp : σ'.pods = σ.pods) (h : S1 keyName opIn σ u) :
    S1 keyName opIn σ' u := by
  unfold S1 at *; rw [hp]; exact h

theorem ownerOk_pods (σ σ' : St) (M : GMap Owner consistency.Rec) (Lr : Nat × Bool) (C : Claims)
    (o : Owner) (u : GoString) (hp : σ'.pods = σ.pods) (h : ownerOk σ M Lr C o u) :
    ownerOk σ' M Lr C o u := by
  obtain ⟨rev, uids, pods, nodes, dss, crs⟩ := σ
  obtain ⟨rev', uids', pods', nodes', dss', crs'⟩ := σ'
  simp only at hp
  subst hp
  obtain ⟨a, b, c, e, f⟩ := h
  exact ⟨a, b, c, e, f⟩

theorem dsAtOwner_dss (σ σ' : St) (hd : σ'.dss = σ.dss) : dsAtOwner σ' = dsAtOwner σ := by
  funext o; unfold dsAtOwner; rw [hd]

/-- **Two versions of a DaemonSet the controller sees alike**: name, namespace and `dsSame`. -/
def dsEq (d d' : kd.apps.DaemonSet) : Prop :=
  d.ObjectMeta'.Name' = d'.ObjectMeta'.Name' ∧ d.ObjectMeta'.Namespace' = d'.ObjectMeta'.Namespace' ∧
    dsSame d d'

theorem dsEq_ctlRef {d d' : kd.apps.DaemonSet} (h : dsEq d d') : ctlRefOf d = ctlRefOf d' := by
  obtain ⟨hn, -, hu, -⟩ := h; unfold ctlRefOf; rw [hn, hu]

theorem dsEq_tmplLabels {d d' : kd.apps.DaemonSet} (h : dsEq d d') :
    dsTmplLabels d = dsTmplLabels d' := by
  obtain ⟨-, -, -, hs, -⟩ := h; unfold dsTmplLabels; rw [hs]

theorem dsEq_hash {d d' : kd.apps.DaemonSet} (h : dsEq d d') : dsHash d = dsHash d' := by
  obtain ⟨-, -, -, hs, -, hc⟩ := h; unfold dsHash; rw [hs, hc]

theorem dsEq_crName {d d' : kd.apps.DaemonSet} (h : dsEq d d') : crName d = crName d' := by
  unfold crName; rw [dsEq_hash h, h.1]

theorem dsEq_sel {d d' : kd.apps.DaemonSet} (h : dsEq d d') : selOf d = selOf d' := by
  obtain ⟨-, -, -, hs, -⟩ := h; unfold selOf; rw [hs]

theorem podOf_dsEq {d d' : kd.apps.DaemonSet} {p : kd.core.Pod} (h : dsEq d d') (hp : podOf d p) :
    podOf d' p :=
  ⟨by rw [← dsEq_ctlRef h]; exact hp.ref, by rw [← h.2.1]; exact hp.ns,
   by rw [← dsEq_tmplLabels h]; exact hp.lbls, by rw [← dsEq_hash h]; exact hp.hash,
   hp.unbound, hp.pending, hp.live, hp.noFin⟩

theorem crOf_dsEq {d d' : kd.apps.DaemonSet} {r : kd.apps.ControllerRevision} (h : dsEq d d')
    (hr : crOf d r) : crOf d' r := by
  have hs := h.2.2.2.1
  exact ⟨by rw [← dsEq_ctlRef h]; exact hr.ref, by rw [← h.2.1]; exact hr.ns,
    by rw [← dsEq_crName h]; exact hr.name,
    by rw [← dsEq_hash h, ← dsEq_tmplLabels h]; exact hr.lbls, by rw [← hs]; exact hr.data⟩

theorem dsWf_dsEq {d d' : kd.apps.DaemonSet} (h : dsEq d d') (w : dsWf d) : dsWf d' := by
  have hn := h.1; have hns := h.2.1; have hs := h.2.2.2.1; have hc := h.2.2.2.2.2
  refine ⟨by rw [← hns, ← hn]; exact w.nsName, by rw [← hns]; exact w.nsNe,
    by rw [← dsEq_sel h]; exact w.selValid, ?_, by rw [← hs]; exact w.unbound,
    by rw [← hs]; exact w.noFin, by rw [← hs]; exact w.histLimit, by rw [← hc]; exact w.noCollision⟩
  intro L hL
  rw [← dsEq_sel h]
  exact w.selCovers L (by rw [dsEq_tmplLabels h]; exact hL)

theorem dsSame_trans {a b c : kd.apps.DaemonSet} (h1 : dsSame a b) (h2 : dsSame b c) :
    dsSame a c := by
  obtain ⟨a1, a2, a3, a4⟩ := h1; obtain ⟨b1, b2, b3, b4⟩ := h2
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4⟩

theorem dsSame_refl (a : kd.apps.DaemonSet) : dsSame a a := ⟨rfl, rfl, rfl, rfl⟩

/-- `podOf` does not depend on the pod's version. -/
theorem podOf_meta (d : kd.apps.DaemonSet) (p : kd.core.Pod) (m : kd.meta.ObjectMeta)
    (h : podOf d p) (hr : m.OwnerReferences' = p.ObjectMeta'.OwnerReferences')
    (hn : m.Namespace' = p.ObjectMeta'.Namespace') (hl : m.Labels' = p.ObjectMeta'.Labels')
    (hdt : m.DeletionTimestamp' = p.ObjectMeta'.DeletionTimestamp')
    (hf : m.Finalizers' = p.ObjectMeta'.Finalizers') : podOf d { p with ObjectMeta' := m } :=
  ⟨by rw [hr]; exact h.ref, by rw [hn]; exact h.ns, by rw [hl]; exact h.lbls,
   by rw [hl]; exact h.hash, h.unbound, h.pending, by rw [hdt]; exact h.live, by rw [hf]; exact h.noFin⟩

/-! ## A create's key is fresh -/

theorem prepareD_ns_name (o : Obj) :
    (prepareD o).meta.Namespace' = o.meta.Namespace' ∧ (prepareD o).meta.Name' = o.meta.Name' := by
  cases o <;> simp [prepareD, preparePodD, prepareDaemonSetD, Obj.meta]

theorem createApply_fresh (r : Res) (ns : GoString) (o : Obj) (σ : St)
    (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) (herr : createErr r ns o σ = none) :
    (σ.tbl r).objs !! (createApply r ns o σ t).1.key = none := by
  have hk : (createApply r ns o σ t).1.key = mkKey (createNs r ns o).meta.Namespace'
      (if (createNs r ns o).meta.Name' = go!"" then
        (createNs r ns o).meta.GenerateName' ++ rvStr (σ.rev + 1)
      else (createNs r ns o).meta.Name') := by
    unfold createApply
    simp only [Obj.key, Obj.modMeta, Obj.meta_setMeta, (prepareD_ns_name _).1,
      (prepareD_ns_name _).2]
  rw [hk]
  unfold createErr at herr
  simp only at herr
  split at herr
  · cases herr
  split at herr
  · cases herr
  split at herr
  · cases herr
  rcases hx : (σ.tbl r).objs !! mkKey (createNs r ns o).meta.Namespace'
      (if (createNs r ns o).meta.Name' = go!"" then
        (createNs r ns o).meta.GenerateName' ++ rvStr (σ.rev + 1)
      else (createNs r ns o).meta.Name') with _ | v
  · rfl
  · rw [hx] at herr; simp at herr

/-- The parts of a create's state. -/
theorem createApply_parts (r : Res) (ns : GoString) (o : Obj) (σ : St)
    (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) :
    ((createApply r ns o σ t).2.tbl r).objs =
        <[(createApply r ns o σ t).1.key := (createApply r ns o σ t).1]> (σ.tbl r).objs ∧
    ((createApply r ns o σ t).2.tbl r).log =
        (σ.tbl r).log ++ [⟨.added, σ.rev + 1, (createApply r ns o σ t).1⟩] ∧
    ∀ r', r' ≠ r → (createApply r ns o σ t).2.tbl r' = σ.tbl r' := by
  refine ⟨?_, ?_, ?_⟩
  · cases r <;> simp [createApply, St.setTbl, St.tbl]
  · cases r <;> simp [createApply, St.setTbl, St.tbl]
  · intro r' hr'; cases r <;> cases r' <;> simp_all [createApply, St.setTbl, St.tbl]

/-! ## The controller's pod create, for its claim -/

/-- **The claimant's pod create** (the claim `(o, n)` empty, the pod the controller makes for the
DaemonSet `d` on `n`): the new pod the claim's, S1 kept. -/
theorem podCreate_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld : Nat) (o : Owner) (d : kd.apps.DaemonSet) (n ns : GoString)
    (dp : kd.core.Pod) (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) (h : s1Ok σ M Lm C Ld)
    (hd : dsAtOwner σ o = some d) (hC : C !! (o, n) = some none)
    (hpod : newPodOk keyName opIn d.ObjectMeta'.UID' n dp)
    (hscene : ∃ q, (createApply .pods ns (.pod dp) σ t).1 = .pod q ∧ podOf d q)
    (herr : createErr .pods ns (.pod dp) σ = none) :
    s1Ok (createApply .pods ns (.pod dp) σ t).2 M Lm
      (<[(o, n) := some (false, (createApply .pods ns (.pod dp) σ t).1.key, (σ.rev + 1).toNat)]> C)
      Ld := by
  have hfresh := createApply_fresh .pods ns (.pod dp) σ t herr
  obtain ⟨-, hon⟩ := createApply_pod keyName opIn d.ObjectMeta'.UID' n ns dp σ t hpod
  obtain ⟨hobjs, hlog, hother⟩ := createApply_parts .pods ns (.pod dp) σ t
  generalize hpd : (createApply .pods ns (.pod dp) σ t) = pr at hfresh hon hobjs hlog hother hscene ⊢
  obtain ⟨p, σ'⟩ := pr
  simp only [St.tbl] at hfresh hon hobjs hlog hscene ⊢
  have hdss : σ'.dss = σ.dss := hother .daemonSets (by decide)
  have hcrs : σ'.crs = σ.crs := hother .revisions (by decide)
  have hadd : ∀ k, addedRv σ'.pods.log k =
      if p.key = k then some (σ.rev + 1).toNat else addedRv σ.pods.log k := by
    intro k; rw [hlog]; exact addedRv_snoc_added _ _ k rfl
  have hdo := dsAtOwner_dss σ σ' hdss
  obtain ⟨q, hq, hqo⟩ := hscene
  have honly : ∀ u', dsPod u' p → u' = d.ObjectMeta'.UID' := by
    intro u' hu'; rw [hq] at hu'; exact podOf_ctlBy hqo hu'
  have hnone : ∀ k o', σ.pods.objs !! k = some o' →
      ¬ dsPodOn keyName opIn d.ObjectMeta'.UID' n o' := by
    intro k o' hk' hdo'
    obtain ⟨w, c, hv, -⟩ := (h.owners o d hd).claims n none hC k o' hk' hdo'
    cases hv
  have hP : ∀ o' k c, pendOf C o' k c →
      pendOf (<[(o, n) := some (false, p.key, (σ.rev + 1).toNat)]> C) o' k c := by
    rintro o' k c ⟨n', w, h'⟩
    refine ⟨n', w, ?_⟩
    simp only [GMap.lookup_insert_eq_iff]
    split
    · rename_i e; rw [← e, hC] at h'; cases h'
    · exact h'
  have hP2 : pendOf (<[(o, n) := some (false, p.key, (σ.rev + 1).toNat)]> C) o p.key
      (σ.rev + 1).toNat := ⟨n, false, by simp⟩
  have huo : ∀ o' d', dsAtOwner σ o' = some d' → d'.ObjectMeta'.UID' = d.ObjectMeta'.UID' →
      o' = o := fun o' d' hd' he => h.scene.uidInj o' o d' d hd' hd he
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- S1
    intro u k1 k2 o1 o2 n' h1 h2 hd1 hd2
    rw [hobjs] at h1 h2
    simp only [GMap.lookup_insert_eq_iff] at h1 h2
    by_cases e1 : p.key = k1 <;> by_cases e2 : p.key = k2
    · exact e1.symm.trans e2
    · simp only [e1, ↓reduceIte, Option.some.injEq] at h1
      simp only [e2, ↓reduceIte] at h2
      subst h1
      obtain rfl := honly u (dsPodOn_dsPod hd1)
      obtain rfl := dsPodOn_node_unique hd1 hon
      exact absurd hd2 (hnone k2 o2 h2)
    · simp only [e2, ↓reduceIte, Option.some.injEq] at h2
      simp only [e1, ↓reduceIte] at h1
      subst h2
      obtain rfl := honly u (dsPodOn_dsPod hd2)
      obtain rfl := dsPodOn_node_unique hd2 hon
      exact absurd hd1 (hnone k1 o1 h1)
    · simp only [e1, e2, ↓reduceIte] at h1 h2
      exact h.s1 u k1 k2 o1 o2 n' h1 h2 hd1 hd2
  · rw [hdss]; exact h.scene.dsFixed
  · rw [hdo]; exact h.scene.dsWf
  · rw [hdo]; exact h.scene.uidInj
  · rw [hdo]; exact h.scene.crNameInj
  · intro c hc
    rw [hlog] at hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨q', o', d', h1, h2, h3⟩ := h.scene.pods c hc
      exact ⟨q', o', d', h1, by rw [hdo]; exact h2, h3⟩
    · simp only [List.mem_singleton] at hc
      subst hc
      exact ⟨q, o, d, hq, by rw [hdo]; exact hd, hqo⟩
  · rw [hcrs, hdo]; exact h.scene.crs
  · -- the owners
    intro o' d' hd'
    rw [hdo] at hd'
    have ho := h.owners o' d' hd'
    refine ⟨?_, ?_, ho.recok, ?_, ?_⟩
    · intro k p' hk hu
      rw [hobjs] at hk
      simp only [GMap.lookup_insert_eq_iff] at hk
      split at hk
      · rename_i e
        simp only [Option.some.injEq] at hk
        subst hk
        obtain rfl := huo o' d' hd' (honly _ hu)
        subst e
        exact ⟨_, by rw [hadd, if_pos rfl], Or.inr (Or.inr hP2)⟩
      · rename_i e
        obtain ⟨c, hc, hcase⟩ := ho.acct k p' hk hu
        refine ⟨c, by rw [hadd, if_neg e]; exact hc, ?_⟩
        rcases hcase with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (hP o' k c h3))
    · intro hr k p' hk hu
      rw [hobjs] at hk
      simp only [GMap.lookup_insert_eq_iff] at hk
      split at hk
      · rename_i e
        simp only [Option.some.injEq] at hk
        subst hk
        obtain rfl := huo o' d' hd' (honly _ hu)
        subst e
        exact ⟨_, by rw [hadd, if_pos rfl], Or.inr hP2⟩
      · rename_i e
        obtain ⟨c, hc, hcase⟩ := ho.ready hr k p' hk hu
        refine ⟨c, by rw [hadd, if_neg e]; exact hc, ?_⟩
        rcases hcase with h1 | h3
        · exact Or.inl h1
        · exact Or.inr (hP o' k c h3)
    · intro n' v hC' k p' hk hon'
      rw [hobjs] at hk
      simp only [GMap.lookup_insert_eq_iff] at hk hC'
      by_cases e : (o, n) = (o', n')
      · simp only [e, ↓reduceIte, Option.some.injEq] at hC'
        subst hC'
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        by_cases e2 : p.key = k
        · subst e2
          exact ⟨false, _, rfl, by rw [hadd, if_pos rfl]⟩
        · simp only [e2, ↓reduceIte] at hk
          rw [hd] at hd'; cases hd'
          exact absurd hon' (hnone k p' hk)
      · simp only [e, ↓reduceIte] at hC'
        by_cases e2 : p.key = k
        · simp only [e2, ↓reduceIte, Option.some.injEq] at hk
          subst hk
          obtain rfl := huo o' d' hd' (honly _ (dsPodOn_dsPod hon'))
          rw [hd] at hd'; cases hd'
          obtain rfl := dsPodOn_node_unique hon' hon
          exact absurd rfl e
        · simp only [e2, ↓reduceIte] at hk
          obtain ⟨w, c, hv, hc⟩ := ho.claims n' v hC' k p' hk hon'
          exact ⟨w, c, hv, by rw [hadd, if_neg e2]; exact hc⟩
    · intro n' k c hC'
      simp only [GMap.lookup_insert_eq_iff] at hC'
      split at hC'
      · simp at hC'
      · exact ho.wrote n' k c hC'
  · intro o' n' v hC'
    rw [hdo]
    simp only [GMap.lookup_insert_eq_iff] at hC'
    split at hC'
    · rename_i e
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      rw [hd]; rfl
    · exact h.claimDs o' n' v hC'
  · intro o' r hr
    rw [hdo, hdss]; exact h.recDs o' r hr

/-- The created pod's version is the next version. -/
theorem podCreate_rv (σ : St) (ns : GoString) (dp : kd.core.Pod)
    (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) (hns : dp.ObjectMeta'.Namespace' = go!"") :
    (createApply .pods ns (.pod dp) σ t).1.meta.ResourceVersion' = rvStr (σ.rev + 1) := by
  simp [createApply, Obj.modMeta, Obj.setMeta, Obj.meta_setMeta, Obj.meta, prepareD, createNs,
    Res.namespaced, preparePodD, hns]

end pure

end dsctl
end EtcdGrove
end Perennial
