/-
**S1's invariant, its pure part, and the steps of a sync that keep it** (pure; phase 5 of
`notes/k8s-daemonset-plan.md`; restated in Stage 3 of the autoverify run for every DaemonSet,
`notes/k8s-daemonset-run/design.md`, "S1's invariant"). Lean-first.

**Every DaemonSet, not one.** The sync's specs are general over the key; the invariant is about
every DaemonSet of the API state, each with its own bookkeeping keyed by its owner (`Owner`, the
consistency store's and the work queue's key): `Main`'s S1 is the instance at its DaemonSet's UID.
One DaemonSet would not do: the sync of any key must not panic, which takes the scenario's facts
(`sceneOk`) for every DaemonSet anyway, and a per-key sync spec over one DaemonSet's invariant would
have to special-case the others.

`s1Ok σ M Lm C` (`S1Inv.lean` holds it with the ghost state):
* `S1` of the API state, for every UID;
* `sceneOk σ` (`Scene.lean`): what the model's API and the controller's writes keep of every object;
* for every stored DaemonSet `d` at owner `o` (`ownerOk`): `acct` (`S1Model.lean`) at the owner's
  bound `lbOf Lm o` (a version the pod informer has reached, raised only by the owner's sync), its
  pending creates the claims of `o` holding a pod (`pendOf C o`); the owner's record, if any, for
  `d`'s UID with well-formed versions (`recOk`); every pod of `d` on a claimed node is the claim's
  pending create (`claimsOk`);
* claims only for stored DaemonSets.

**The claims** `C : (owner, node) ↦ none | some (pod key, version)`: a node a sync of the owner
found free (no pod of the DaemonSet in a pod cache covering the API state's pods of it) and hands
to a create goroutine; `none` until the goroutine's create commits, then the pod's key and version
(pending) until its `WroteAt` accounts for it and the claim goes.

The steps (stated; their proofs are Stage 4's invariant walk-through):
* `claim_step`: a free node claimed;
* `create_step`: the claimant's create: the new pod pending, S1 kept;
* `wrote_step`: the claimant's `WroteAt` of its pod's version: the claim goes, the record covers the
  pod;
* `unclaim_step`: a claim with no pod goes (a create with no effect);
* `ensureReady_step`: `EnsureReady` succeeding: the owner's record goes, its bound rises.
There is **no step for an ambiguous create**: the pod was written, the call returned the timeout,
so the goroutine has no version to record and its claim cannot go
(`S1Model.ambiguous_create_breaks_S1`).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Model
public import Proof.k8s_io.kubernetes.pkg.controller.daemon.Scene
public import Proof.k8s_io.kubernetes.pkg.controller.daemon.RvLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open apimodel informer consistency resourceversion

section pure
variable [GooseExts]

/-- **The claims**: (owner, node) ↦ the claimant's pod (key, version) once created. -/
abbrev Claims : Type := GMap (Owner × GoString) (Option (Key × Nat))

/-- The owner's pending creates as `acct`'s predicate: the claims of `o` holding a pod. -/
def pendOf (C : Claims) (o : Owner) (k : Key) (c : Nat) : Prop :=
  ∃ n, C !! (o, n) = some (some (k, c))

/-- **The owner's claimed nodes are free**: every pod of `u` on a node `n` the owner claimed is the
claim's pod (its key and the version it was added at). -/
def claimsOk (σ : St) (C : Claims) (o : Owner) (u : GoString) : Prop :=
  ∀ n v, C !! (o, n) = some v → ∀ k p, σ.pods.objs !! k = some p → dsPodOn keyName opIn u n p →
    ∃ c, v = some (k, c) ∧ addedRv σ.pods.log k = some c

/-- The record, if any, is for `u` and its versions are well formed. -/
def recOk (rc : Option consistency.Rec) (u : GoString) : Prop :=
  ∀ r, rc = some r → r.uid = u ∧ vsWf r.vs

/-- **One owner's bookkeeping** (its DaemonSet's UID `u`, its bound `L`). -/
structure ownerOk (σ : St) (M : GMap Owner consistency.Rec) (L : Nat) (C : Claims) (o : Owner)
    (u : GoString) : Prop where
  acct : acct σ u L (M !! o) (pendOf C o)
  recok : recOk (M !! o) u
  claims : claimsOk σ C o u

/-- The owner's bound (`0` for an owner never synced). -/
def lbOf (Lm : GMap Owner Nat) (o : Owner) : Nat := (Lm !! o).getD 0

/-- **The pure invariant.** -/
structure s1Ok (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner Nat) (C : Claims) :
    Prop where
  s1 : ∀ u, S1 keyName opIn σ u
  scene : sceneOk σ
  owners : ∀ o d, dsAtOwner σ o = some d → ownerOk σ M (lbOf Lm o) C o d.ObjectMeta'.UID'
  claimDs : ∀ o n v, C !! (o, n) = some v → (dsAtOwner σ o).isSome

/-- A pod of the DaemonSet targets one node. -/
theorem dsPodOn_node_unique {K Op u n n' : GoString} {o : Obj} (h1 : dsPodOn K Op u n' o)
    (h2 : dsPodOn K Op u n o) : n' = n := by
  cases o with
  | pod dd => exact Option.some.inj (h1.2.symm.trans h2.2)
  | _ => exact h1.elim

/-- **The initial state**: a server with no pods, DaemonSets or revisions (`Main` allocates the
invariant after the admin's node create), no record, no bound, no claim. -/
theorem s1Ok_init (σ : St) (hp : σ.pods.log = []) (hpo : σ.pods.objs = ∅)
    (hd : σ.dss.log = []) (hdo : σ.dss.objs = ∅) (hc : σ.crs.log = []) :
    s1Ok σ ∅ ∅ ∅ := by
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro u k1 k2 o1 o2 n h1; simp [hpo] at h1
  · intro c hc'; simp [hd] at hc'
  · intro o d h; simp [dsAtOwner, hdo] at h
  · intro o o' d d' h; simp [dsAtOwner, hdo] at h
  · intro o o' d d' h; simp [dsAtOwner, hdo] at h
  · intro c hc'; simp [hp] at hc'
  · intro c hc'; simp [hc] at hc'
  · intro o d h; simp [dsAtOwner, hdo] at h
  · intro o n v h; simp at h

/-! ### The steps (stated; proofs in Stage 4) -/

/-- **A free node claimed** by the owner `o` (its DaemonSet `d`): the node has no pod of `d` in the
API state (the sync's pod cache covers its pods: `acct` with nothing pending and no record). -/
theorem claim_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner Nat) (C : Claims)
    (o : Owner) (d : kd.apps.DaemonSet) (n : GoString) (h : s1Ok σ M Lm C)
    (hd : dsAtOwner σ o = some d) (hn : C !! (o, n) = none)
    (hfree : ∀ k p, σ.pods.objs !! k = some p → ¬ dsPodOn keyName opIn d.ObjectMeta'.UID' n p) :
    s1Ok σ M Lm (<[(o, n) := none]> C) := by
  sorry

/-- **The claimant's create** (the claim `(o, n)` empty): the new pod pending under the claim, S1
kept. -/
theorem create_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner Nat) (C : Claims)
    (o : Owner) (d : kd.apps.DaemonSet) (n ns : GoString) (dp : kd.core.Pod)
    (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) (h : s1Ok σ M Lm C)
    (hd : dsAtOwner σ o = some d) (hC : C !! (o, n) = some none)
    (hpod : newPodOk keyName opIn d.ObjectMeta'.UID' n dp ∧ podOf d (preparePodD dp))
    (herr : createErr .pods ns (.pod dp) σ = none) :
    let p := (createApply .pods ns (.pod dp) σ t).1
    let σ' := (createApply .pods ns (.pod dp) σ t).2
    s1Ok σ' M Lm (<[(o, n) := some (p.key, (σ.rev + 1).toNat)]> C) ∧
      p.meta.ResourceVersion' = rvStr (σ.rev + 1) := by
  sorry

/-- **The claimant's `WroteAt`** of its pod's version `rvStr c`, for the owner and its
DaemonSet's UID: the claim goes; the record covers the pod. -/
theorem wrote_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner Nat) (C : Claims)
    (o : Owner) (d : kd.apps.DaemonSet) (n : GoString) (k : Key) (c : w64) (h : s1Ok σ M Lm C)
    (hd : dsAtOwner σ o = some d) (hC : C !! (o, n) = some (some (k, c.toNat)))
    (hc : 1 ≤ c.toNat) :
    s1Ok σ (wroteAtM M o d.ObjectMeta'.UID' podGR (rvStr c)) Lm (GMap.delete (o, n) C) := by
  sorry

/-- **A claim with no pod goes** (the claimant's create had no effect). -/
theorem unclaim_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner Nat) (C : Claims)
    (o : Owner) (n : GoString) (h : s1Ok σ M Lm C) (hC : C !! (o, n) = some none) :
    s1Ok σ M Lm (GMap.delete (o, n) C) := by
  sorry

/-- **`EnsureReady(o)` succeeding** with no claim of `o` (the owner's sync holds its token whole):
the record goes, the owner's bound rises to `L'`, a version the pods' store has reached that is at
least every recorded pod version (`readyPods`). -/
theorem ensureReady_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner Nat)
    (C : Claims) (o : Owner) (L' : Nat) (h : s1Ok σ M Lm C)
    (hnc : ∀ n v, C !! (o, n) ≠ some v) (hL : lbOf Lm o ≤ L') (hr : readyPods (M !! o) L') :
    s1Ok σ (GMap.delete o M) (<[o := L']> Lm) C := by
  sorry

end pure

end dsctl
end EtcdGrove
end Perennial
