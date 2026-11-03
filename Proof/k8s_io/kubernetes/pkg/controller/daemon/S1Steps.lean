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
* for every stored DaemonSet `d` at owner `o` (`ownerOk`), with the owner's bound and ready flag
  `lbOf Lm o` (a version the pod informer has reached, changed only by the owner's sync): `acct`
  (`S1Model.lean`), its pending creates the claims of `o` holding a pod (`pendOf C o`); if ready
  (its sync's `EnsureReady` passed), every pod of `d` at most the bound or a claim's
  (`readyAcct`: what lets the sync claim a node its pod cache shows free); the owner's record, if
  any, for `d`'s UID with well-formed versions (`recOk`); every pod of `d` on a claimed node is the
  claim's (`claimsOk`); a written claim's pod covered by the record (`wroteOk`);
* claims only for stored DaemonSets.

**The claims** `C : (owner, node) ↦ none | some (written, pod key, version)`: a node a ready sync
of the owner found free (no pod of the DaemonSet in a pod cache covering the API state's pods of
it) and hands to a create goroutine; `none` until the goroutine's create commits, then the pod's
key and version, written once its `WroteAt` ran; the sync releases its claims at the end of its
creates (a written one makes the owner not ready).

The steps (stated; their proofs are Stage 4's invariant walk-through):
* `ensureReady_step`: `EnsureReady` succeeding: the owner's record goes, its bound rises, it is
  ready;
* `claim_step`: a free node claimed;
* `create_step`: the claimant's create: the new pod a claim's, S1 kept;
* `wrote_step`: the claimant's `WroteAt` of its pod's version: the record covers the pod;
* `unclaim_step`: a claim with no pod goes (a create with no effect);
* `release_step`: a written claim goes.
There is **no step for an ambiguous create**: the pod was written, the call returned the timeout,
so the goroutine has no version to record and its claim can neither be written nor released
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

/-- **The claims**: (owner, node) ↦ `none` (claimed, no pod yet) or `some (w, k, c)`: the
claimant's pod at key `k`, added at version `c`, with `w` whether its `WroteAt` ran. -/
abbrev Claims : Type := GMap (Owner × GoString) (Option (Bool × Key × Nat))

/-- The owner's pending creates as `acct`'s predicate: the claims of `o` holding a pod. -/
def pendOf (C : Claims) (o : Owner) (k : Key) (c : Nat) : Prop :=
  ∃ n w, C !! (o, n) = some (some (w, k, c))

/-- **The owner's claimed nodes are free**: every pod of `u` on a node `n` the owner claimed is the
claim's pod (its key and the version it was added at). -/
def claimsOk (σ : St) (C : Claims) (o : Owner) (u : GoString) : Prop :=
  ∀ n v, C !! (o, n) = some v → ∀ k p, σ.pods.objs !! k = some p → dsPodOn keyName opIn u n p →
    ∃ w c, v = some (w, k, c) ∧ addedRv σ.pods.log k = some c

/-- **A written claim's pod is covered by the owner's record.** -/
def wroteOk (M : GMap Owner consistency.Rec) (C : Claims) (o : Owner) : Prop :=
  ∀ n k c, C !! (o, n) = some (some (true, k, c)) → recCovers (M !! o) c

/-- **The owner is ready** (its sync's `EnsureReady` passed and no claim was released since): every
pod of `u` was added at a version at most the bound, or is a claim's. -/
def readyAcct (σ : St) (u : GoString) (L : Nat) (C : Claims) (o : Owner) : Prop :=
  ∀ k p, σ.pods.objs !! k = some p → dsPod u p →
    ∃ c, addedRv σ.pods.log k = some c ∧ (c ≤ L ∨ pendOf C o k c)

/-- The record, if any, is for `u` and its versions are well formed. -/
def recOk (rc : Option consistency.Rec) (u : GoString) : Prop :=
  ∀ r, rc = some r → r.uid = u ∧ vsWf r.vs

/-- **One owner's bookkeeping** (its DaemonSet's UID `u`; its bound `Lr.1` and ready flag
`Lr.2`). -/
structure ownerOk (σ : St) (M : GMap Owner consistency.Rec) (Lr : Nat × Bool) (C : Claims)
    (o : Owner) (u : GoString) : Prop where
  acct : acct σ u Lr.1 (M !! o) (pendOf C o)
  ready : Lr.2 = true → readyAcct σ u Lr.1 C o
  recok : recOk (M !! o) u
  claims : claimsOk σ C o u
  wrote : wroteOk M C o

/-- The owner's bound and ready flag (`(0, false)` for an owner never synced). -/
def lbOf (Lm : GMap Owner (Nat × Bool)) (o : Owner) : Nat × Bool := (Lm !! o).getD (0, false)

/-- **The pure invariant.** -/
structure s1Ok (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) : Prop where
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

/-- **`EnsureReady(o)` succeeding** with no claim of `o` (the owner's sync holds its token whole):
the record goes; the owner's bound rises to `L'`, a version the pods' store has reached that is at
least every recorded pod version (`readyPods`); the owner is ready. -/
theorem ensureReady_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (o : Owner) (L' : Nat) (h : s1Ok σ M Lm C)
    (hnc : ∀ n, C !! (o, n) = none) (hL : (lbOf Lm o).1 ≤ L') (hr : readyPods (M !! o) L') :
    s1Ok σ (GMap.delete o M) (<[o := (L', true)]> Lm) C := by
  sorry

/-- **A free node claimed** by the ready owner `o` (its DaemonSet `d`): no pod of `d` on `n` was
added at a version at most the bound (the sync's pod cache, at a version at least the bound, shows
none) and the owner has no claim on `n`. -/
theorem claim_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (o : Owner) (d : kd.apps.DaemonSet) (n : GoString) (h : s1Ok σ M Lm C)
    (hd : dsAtOwner σ o = some d) (hn : C !! (o, n) = none) (hready : (lbOf Lm o).2 = true)
    (hfree : ∀ k p c, σ.pods.objs !! k = some p → dsPodOn keyName opIn d.ObjectMeta'.UID' n p →
      addedRv σ.pods.log k = some c → (lbOf Lm o).1 < c) :
    s1Ok σ M Lm (<[(o, n) := none]> C) := by
  sorry

/-- **The claimant's create** (the claim `(o, n)` empty): the new pod a claim's, S1 kept. -/
theorem create_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (o : Owner) (d : kd.apps.DaemonSet) (n ns : GoString) (dp : kd.core.Pod)
    (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) (h : s1Ok σ M Lm C)
    (hd : dsAtOwner σ o = some d) (hC : C !! (o, n) = some none)
    (hpod : newPodOk keyName opIn d.ObjectMeta'.UID' n dp)
    (hscene : ∀ p, (createApply .pods ns (.pod dp) σ t).1 = .pod p → podOf d p)
    (herr : createErr .pods ns (.pod dp) σ = none) :
    let p := (createApply .pods ns (.pod dp) σ t).1
    let σ' := (createApply .pods ns (.pod dp) σ t).2
    s1Ok σ' M Lm (<[(o, n) := some (false, p.key, (σ.rev + 1).toNat)]> C) ∧
      p.meta.ResourceVersion' = rvStr (σ.rev + 1) := by
  sorry

/-- **The claimant's `WroteAt`** of its pod's version `rvStr c`, for the owner and its
DaemonSet's UID: the record covers the pod, the claim is written. -/
theorem wrote_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (o : Owner) (d : kd.apps.DaemonSet) (n : GoString) (k : Key) (c : w64)
    (h : s1Ok σ M Lm C) (hd : dsAtOwner σ o = some d)
    (hC : C !! (o, n) = some (some (false, k, c.toNat))) (hc : 1 ≤ c.toNat) :
    s1Ok σ (wroteAtM M o d.ObjectMeta'.UID' podGR (rvStr c)) Lm
      (<[(o, n) := some (true, k, c.toNat)]> C) := by
  sorry

/-- **A claim with no pod goes** (the claimant's create had no effect, or the claim was never
used). -/
theorem unclaim_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (o : Owner) (n : GoString) (h : s1Ok σ M Lm C) (hC : C !! (o, n) = some none) :
    s1Ok σ M Lm (GMap.delete (o, n) C) := by
  sorry

/-- **A written claim released** (by the sync, after its creates): the owner is no longer ready. -/
theorem release_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (o : Owner) (n : GoString) (k : Key) (c : Nat) (h : s1Ok σ M Lm C)
    (hC : C !! (o, n) = some (some (true, k, c))) :
    s1Ok σ M (<[o := ((lbOf Lm o).1, false)]> Lm) (GMap.delete (o, n) C) := by
  sorry

end pure

end dsctl
end EtcdGrove
end Perennial
