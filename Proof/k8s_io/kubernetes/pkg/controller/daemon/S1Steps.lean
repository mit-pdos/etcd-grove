/-
**S1's invariant, its pure part, and the bookkeeping steps that keep it** (pure; phase 5 of
`notes/k8s-daemonset-plan.md`; restated in Stage 3 of the autoverify run for every DaemonSet,
`notes/k8s-daemonset-run/design.md`, "S1's invariant"). Lean-first.

**Every DaemonSet, not one.** The sync's specs are general over the key; the invariant is about
every DaemonSet of the API state, each with its own bookkeeping keyed by its owner (`Owner`, the
consistency store's and the work queue's key): `Main`'s S1 is the instance at its DaemonSet's UID.
One DaemonSet would not do: the sync of any key must not panic, which takes the scenario's facts
(`sceneOk`) for every DaemonSet anyway, and a per-key sync spec over one DaemonSet's invariant would
have to special-case the others.

`s1Ok σ M Lm C Ld` (`S1Inv.lean` holds it with the ghost state):
* `S1` of the API state, for every UID;
* `sceneOk σ` (`Scene.lean`): what the model's API and the controller's writes keep of every object;
* for every stored DaemonSet `d` at owner `o` (`ownerOk`), with the owner's bound and ready flag
  `lbOf Lm o` (a version the pod informer has reached, changed only by the owner's sync): `acct`
  (`S1Model.lean`), its pending creates the claims of `o` holding a pod (`pendOf C o`); if ready
  (its sync's `EnsureReady` passed), every pod of `d` at most the bound or a claim's
  (`readyAcct`: what lets the sync claim a node its pod cache shows free); the owner's record, if
  any, for `d`'s UID with well-formed versions (`recOk`); every pod of `d` on a claimed node is the
  claim's (`claimsOk`); a written claim's pod covered by the record (`wroteOk`);
* claims only for stored DaemonSets;
* a record only for a stored DaemonSet with a change logged at a version at most `Ld`, a version
  the DaemonSet informer has reached (`recDs`, `dsSeenBy`): so a sync whose DaemonSet cache (at a
  version at least `Ld`) does not show its DaemonSet finds no record to lose in its `Clear`
  (`clear_notfound_noop`).

**The claims** `C : (owner, node) ↦ none | some (written, pod key, version)`: a node a ready sync
of the owner found free (no pod of the DaemonSet in a pod cache covering the API state's pods of
it) and hands to a create goroutine; `none` until the goroutine's create commits, then the pod's
key and version, written once its `WroteAt` ran; the sync releases its claims at the end of its
creates (a written one makes the owner not ready).

The bookkeeping steps (this file; the API writes' steps are `S1Writes.lean`):
* `register_step`: an owner's first sync registers it (bound `0`, not ready);
* `raiseLd_step`: the DaemonSet informer's bound rises;
* `ensureReady_step`: `EnsureReady` succeeding: the owner's record goes, its bound rises, it is
  ready (`EnsureReady` failing changes nothing);
* `claim_step`: a free node claimed;
* `wrote_step`: the claimant's `WroteAt` of its pod's version: the record covers the pod, the claim
  is written; `wroteAt_step`: any other `WroteAt` of the owner's sync (the DaemonSet's status);
* `unclaim_step`: a claim with no pod goes (a create with no effect);
* `release_step`: a written claim goes;
* `clear_noop`, `clear_notfound_noop`: the consistency store's `Clear` changes nothing: for an owner
  with no DaemonSet or another UID (`deleteDaemonset`'s), or one whose sync's DaemonSet cache does
  not show it (`syncDaemonSet`'s `NotFound`).
There is **no step for an ambiguous create**: the pod was written, the call returned the timeout,
so the goroutine has no version to record and its claim can neither be written nor released
(`S1Model.ambiguous_create_breaks_S1`).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Model
public import Proof.k8s_io.kubernetes.pkg.controller.daemon.Scene
public import Proof.k8s_io.kubernetes.pkg.controller.daemon.RvLemmas

@[expose] public section

set_option autoImplicit false

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

/-- **Owner `o`'s DaemonSet has a change logged at a version at most `Ld`** (a DaemonSet cache at a
version at least `Ld` shows it: DaemonSets are never deleted). -/
def dsSeenBy (σ : St) (o : Owner) (Ld : Nat) : Prop :=
  ∃ c ∈ σ.dss.log, c.obj.key = o ∧ c.rv.toNat ≤ Ld

theorem dsSeenBy_mono {σ : St} {o : Owner} {Ld Ld' : Nat} (h : dsSeenBy σ o Ld) (hle : Ld ≤ Ld') :
    dsSeenBy σ o Ld' := by
  obtain ⟨c, hc, hk, hl⟩ := h
  exact ⟨c, hc, hk, Nat.le_trans hl hle⟩

theorem dsSeenBy_log {σ σ' : St} {o : Owner} {Ld : Nat} (h : dsSeenBy σ o Ld)
    (hl : ∀ c ∈ σ.dss.log, c ∈ σ'.dss.log) : dsSeenBy σ' o Ld := by
  obtain ⟨c, hc, hk, hle⟩ := h
  exact ⟨c, hl c hc, hk, hle⟩

/-- **The pure invariant.** -/
structure s1Ok (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld : Nat) : Prop where
  s1 : ∀ u, S1 keyName opIn σ u
  scene : sceneOk σ
  owners : ∀ o d, dsAtOwner σ o = some d → ownerOk σ M (lbOf Lm o) C o d.ObjectMeta'.UID'
  claimDs : ∀ o n v, C !! (o, n) = some v → (dsAtOwner σ o).isSome
  recDs : ∀ o r, M !! o = some r → (dsAtOwner σ o).isSome ∧ dsSeenBy σ o Ld

/-- A pod of the DaemonSet targets one node. -/
theorem dsPodOn_node_unique {K Op u n n' : GoString} {o : Obj} (h1 : dsPodOn K Op u n' o)
    (h2 : dsPodOn K Op u n o) : n' = n := by
  cases o with
  | pod dd => exact Option.some.inj (h1.2.symm.trans h2.2)
  | _ => exact h1.elim

/-- **The initial state**: a server with no pods, DaemonSets or revisions (`Main` allocates the
invariant after the admin's node create), no record, no bound, no claim. -/
theorem s1Ok_init (σ : St) (hp : σ.pods.log = []) (hpo : σ.pods.objs = ∅)
    (hd : σ.dss.log = []) (hdo : σ.dss.objs = ∅) (hc : σ.crs.log = []) (Ld : Nat) :
    s1Ok σ ∅ ∅ ∅ Ld := by
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro u k1 k2 o1 o2 n h1; simp [hpo] at h1
  · intro c hc'; simp [hd] at hc'
  · intro o d h; simp [dsAtOwner, hdo] at h
  · intro o o' d d' h; simp [dsAtOwner, hdo] at h
  · intro o o' d d' h; simp [dsAtOwner, hdo] at h
  · intro c hc'; simp [hp] at hc'
  · intro c hc'; simp [hc] at hc'
  · intro o d h; simp [dsAtOwner, hdo] at h
  · intro o n v h; simp at h
  · intro o r h; simp at h

/-! ### Small facts -/

theorem pendOf_insert_none (C : Claims) (o o' : Owner) (n : GoString) (k : Key) (c : Nat)
    (hn : ∀ v, C !! (o, n) = some v → v = none) :
    pendOf (<[(o, n) := none]> C) o' k c ↔ pendOf C o' k c := by
  unfold pendOf
  constructor
  · rintro ⟨n', w, h⟩
    refine ⟨n', w, ?_⟩
    simp only [GMap.lookup_insert_eq_iff] at h
    split at h
    · cases h
    · exact h
  · rintro ⟨n', w, h⟩
    refine ⟨n', w, ?_⟩
    simp only [GMap.lookup_insert_eq_iff]
    split
    · rename_i e; rw [← e] at h; cases hn _ h
    · exact h

theorem pendOf_delete_none (C : Claims) (o o' : Owner) (n : GoString) (k : Key) (c : Nat)
    (hn : C !! (o, n) = some none) :
    pendOf (GMap.delete (o, n) C) o' k c ↔ pendOf C o' k c := by
  unfold pendOf
  constructor
  · rintro ⟨n', w, h⟩
    refine ⟨n', w, ?_⟩
    simp only [GMap.lookup_delete_iff] at h
    split at h
    · cases h
    · exact h
  · rintro ⟨n', w, h⟩
    refine ⟨n', w, ?_⟩
    simp only [GMap.lookup_delete_iff]
    split
    · rename_i e; rw [← e, hn] at h; cases h
    · exact h

/-- Writing a claim keeps its pod pending. -/
theorem pendOf_write (C : Claims) (o o' : Owner) (n : GoString) (k k' : Key) (c c' : Nat)
    (hC : C !! (o, n) = some (some (false, k, c))) :
    pendOf (<[(o, n) := some (true, k, c)]> C) o' k' c' ↔ pendOf C o' k' c' := by
  unfold pendOf
  constructor
  · rintro ⟨n', w, h⟩
    simp only [GMap.lookup_insert_eq_iff] at h
    split at h
    · rename_i e
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact ⟨n', false, by rw [← e]; exact hC⟩
    · exact ⟨n', w, h⟩
  · rintro ⟨n', w, h⟩
    by_cases e : (o, n) = (o', n')
    · rw [← e, hC] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact ⟨n', true, by simp [e]⟩
    · exact ⟨n', w, by simp only [GMap.lookup_insert_eq_iff, e, ↓reduceIte]; exact h⟩

theorem readyAcct_congr (σ : St) (u : GoString) (L : Nat) (C C' : Claims) (o : Owner)
    (hP : ∀ k c, pendOf C' o k c ↔ pendOf C o k c) :
    readyAcct σ u L C' o ↔ readyAcct σ u L C o := by
  unfold readyAcct
  simp only [hP]

theorem lbOf_insert_ne (Lm : GMap Owner (Nat × Bool)) {o o' : Owner} (x : Nat × Bool)
    (h : o ≠ o') : lbOf (<[o := x]> Lm) o' = lbOf Lm o' := by
  unfold lbOf; rw [GMap.lookup_insert_ne _ _ h]

theorem lbOf_insert_eq (Lm : GMap Owner (Nat × Bool)) (o : Owner) (x : Nat × Bool) :
    lbOf (<[o := x]> Lm) o = x := by
  unfold lbOf; simp

/-- The owner's record, after its sync's `WroteAt` (any group resource and version, its
DaemonSet's UID): still for `u`, well formed, covering what it covered. -/
theorem ownerOk_wroteAt (σ : St) (M : GMap Owner consistency.Rec) (Lr : Nat × Bool) (C : Claims)
    (o o' : Owner) (u uo : GoString) (gr : GR) (rv : GoString) (h : ownerOk σ M Lr C o' uo)
    (hu : o = o' → uo = u) :
    ownerOk σ (wroteAtM M o u gr rv) Lr C o' uo := by
  by_cases e : o = o'
  · subst e
    obtain rfl := hu rfl
    have huid : ∀ r, M !! o = some r → r.uid = uo := fun r hr => (h.recok r hr).1
    have hcov : ∀ c, recCovers (M !! o) c → recCovers ((wroteAtM M o uo gr rv) !! o) c :=
      fun c hc => recCovers_wroteAt M o uo gr rv c huid hc
    refine ⟨?_, h.ready, ?_, h.claims, ?_⟩
    · intro k p hk hu'
      obtain ⟨c, hc, hcase⟩ := h.acct k p hk hu'
      refine ⟨c, hc, ?_⟩
      rcases hcase with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr (Or.inl (hcov c h2))
      · exact Or.inr (Or.inr h3)
    · intro r hr
      unfold wroteAtM at hr
      simp only [GMap.lookup_insert_eq, Option.some.injEq] at hr
      subst hr
      refine ⟨rfl, wroteAtVs_wf _ _ _ ?_⟩
      unfold recFor
      split
      · rename_i r hr
        split
        · exact (h.recok r hr).2
        · intro gr x hx; simp at hx
      · intro gr x hx; simp at hx
    · intro n k c hC
      exact hcov c (h.wrote n k c hC)
  · have hM : (wroteAtM M o u gr rv) !! o' = M !! o' := by
      unfold wroteAtM; rw [GMap.lookup_insert_ne _ _ e]
    refine ⟨?_, h.ready, ?_, h.claims, ?_⟩
    · rw [hM]; exact h.acct
    · rw [hM]; exact h.recok
    · intro n k c hC; rw [hM]; exact h.wrote n k c hC

/-! ### The bookkeeping steps -/

/-- **An owner registered** (its first sync): bound `0`, not ready, as for an unregistered one. -/
theorem register_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld : Nat) (o : Owner) (h : s1Ok σ M Lm C Ld) (hn : Lm !! o = none) :
    s1Ok σ M (<[o := (0, false)]> Lm) C Ld := by
  have hlb : ∀ o', lbOf (<[o := (0, false)]> Lm) o' = lbOf Lm o' := by
    intro o'
    by_cases e : o = o'
    · subst e; rw [lbOf_insert_eq]; unfold lbOf; rw [hn]; rfl
    · exact lbOf_insert_ne Lm _ e
  exact ⟨h.s1, h.scene, fun o' d hd => by rw [hlb]; exact h.owners o' d hd, h.claimDs, h.recDs⟩

/-- **The DaemonSet informer's bound rises.** -/
theorem raiseLd_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld Ld' : Nat) (h : s1Ok σ M Lm C Ld) (hle : Ld ≤ Ld') :
    s1Ok σ M Lm C Ld' := by
  refine ⟨h.s1, h.scene, h.owners, h.claimDs, ?_⟩
  intro o r hr
  obtain ⟨h1, h2⟩ := h.recDs o r hr
  exact ⟨h1, dsSeenBy_mono h2 hle⟩

/-- **`EnsureReady(o)` succeeding** with no claim of `o` (the owner's sync holds its token whole):
the record goes; the owner's bound rises to `L'`, a version the pods' store has reached that is at
least every recorded pod version (`readyPods`); the owner is ready. -/
theorem ensureReady_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld : Nat) (o : Owner) (L' : Nat) (h : s1Ok σ M Lm C Ld)
    (hnc : ∀ n, C !! (o, n) = none) (hL : (lbOf Lm o).1 ≤ L') (hr : readyPods (M !! o) L') :
    s1Ok σ (GMap.delete o M) (<[o := (L', true)]> Lm) C Ld := by
  refine ⟨h.s1, h.scene, ?_, h.claimDs, ?_⟩
  · intro o' d hd
    have ho := h.owners o' d hd
    by_cases e : o = o'
    · subst e
      rw [lbOf_insert_eq]
      have hM : (GMap.delete o M) !! o = none := GMap.lookup_delete _ _
      have hacc : dsctl.acct σ d.ObjectMeta'.UID' L' none (pendOf C o) :=
        acct_ensureReady σ _ _ L' _ _ ho.acct hL hr
      refine ⟨(by rw [hM]; exact hacc), ?_, (by rw [hM]; intro r hr'; cases hr'), ho.claims, ?_⟩
      · intro _ k p hk hu
        obtain ⟨c, hc, hcase⟩ := hacc k p hk hu
        refine ⟨c, hc, ?_⟩
        rcases hcase with h1 | ⟨r, -, hr', -⟩ | h3
        · exact Or.inl h1
        · cases hr'
        · exact Or.inr h3
      · intro n k c hC; rw [hnc n] at hC; cases hC
    · have hM : (GMap.delete o M) !! o' = M !! o' := GMap.lookup_delete_ne _ e
      rw [lbOf_insert_ne _ _ e]
      refine ⟨by rw [hM]; exact ho.acct, ho.ready, by rw [hM]; exact ho.recok, ho.claims, ?_⟩
      intro n k c hC; rw [hM]; exact ho.wrote n k c hC
  · intro o' r hr
    simp only [GMap.lookup_delete_iff] at hr
    split at hr
    · cases hr
    · exact h.recDs o' r hr

/-- **A free node claimed** by the ready owner `o` (its DaemonSet `d`), none of whose claims holds
a pod yet (the sync claims every node before its first create): no pod of `d` on `n` was added at
a version at most the bound (the sync's pod cache, at a version at least the bound, shows none). -/
theorem claim_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld : Nat) (o : Owner) (d : kd.apps.DaemonSet) (n : GoString)
    (h : s1Ok σ M Lm C Ld) (hd : dsAtOwner σ o = some d) (hn : C !! (o, n) = none)
    (hready : (lbOf Lm o).2 = true)
    (hnc : ∀ n' w k c, C !! (o, n') ≠ some (some (w, k, c)))
    (hfree : ∀ k p c, σ.pods.objs !! k = some p → dsPodOn keyName opIn d.ObjectMeta'.UID' n p →
      addedRv σ.pods.log k = some c → (lbOf Lm o).1 < c) :
    s1Ok σ M Lm (<[(o, n) := none]> C) Ld := by
  have hpend : ∀ o' k c, pendOf (<[(o, n) := none]> C) o' k c ↔ pendOf C o' k c :=
    fun o' k c => pendOf_insert_none C o o' n k c (by intro v hv; rw [hn] at hv; cases hv)
  refine ⟨h.s1, h.scene, ?_, ?_, h.recDs⟩
  · intro o' d' hd'
    have ho := h.owners o' d' hd'
    have hP : pendOf (<[(o, n) := none]> C) o' = pendOf C o' := by
      funext k c; exact propext (hpend o' k c)
    refine ⟨(by rw [hP]; exact ho.acct),
      (fun hr => (readyAcct_congr _ _ _ _ _ _ (fun k c => by rw [hP])).2 (ho.ready hr)),
      ho.recok, ?_, ?_⟩
    · intro n' v hC k p hk hon
      simp only [GMap.lookup_insert_eq_iff] at hC
      split at hC
      · rename_i e
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rw [hd] at hd'; cases hd'
        exfalso
        obtain ⟨c, hc, hcase⟩ := ho.ready hready k p hk (dsPodOn_dsPod hon)
        rcases hcase with h1 | ⟨n'', w, hC'⟩
        · exact absurd h1 (Nat.not_le.mpr (hfree k p c hk hon hc))
        · exact hnc n'' w k c hC'
      · exact ho.claims n' v hC k p hk hon
    · intro n' k c hC
      simp only [GMap.lookup_insert_eq_iff] at hC
      split at hC
      · cases hC
      · exact ho.wrote n' k c hC
  · intro o' n' v hC
    simp only [GMap.lookup_insert_eq_iff] at hC
    split at hC
    · rename_i e
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      rw [hd]; rfl
    · exact h.claimDs o' n' v hC

/-- **A claim with no pod goes** (the claimant's create had no effect, or the claim was never
used). -/
theorem unclaim_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld : Nat) (o : Owner) (n : GoString) (h : s1Ok σ M Lm C Ld)
    (hC : C !! (o, n) = some none) :
    s1Ok σ M Lm (GMap.delete (o, n) C) Ld := by
  refine ⟨h.s1, h.scene, ?_, ?_, h.recDs⟩
  · intro o' d' hd'
    have ho := h.owners o' d' hd'
    have hP : pendOf (GMap.delete (o, n) C) o' = pendOf C o' := by
      funext k c; exact propext (pendOf_delete_none C o o' n k c hC)
    refine ⟨(by rw [hP]; exact ho.acct),
      (fun hr => (readyAcct_congr _ _ _ _ _ _ (fun k c => by rw [hP])).2 (ho.ready hr)),
      ho.recok, ?_, ?_⟩
    · intro n' v hC' k p hk hon
      simp only [GMap.lookup_delete_iff] at hC'
      split at hC'
      · cases hC'
      · exact ho.claims n' v hC' k p hk hon
    · intro n' k c hC'
      simp only [GMap.lookup_delete_iff] at hC'
      split at hC'
      · cases hC'
      · exact ho.wrote n' k c hC'
  · intro o' n' v hC'
    simp only [GMap.lookup_delete_iff] at hC'
    split at hC'
    · cases hC'
    · exact h.claimDs o' n' v hC'

/-- **A `WroteAt` of the owner's sync** for its DaemonSet's UID (the DaemonSet's status: any group
resource and version), the DaemonSet seen by version `Ld` (`dsSeenBy`). -/
theorem wroteAt_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld : Nat) (o : Owner) (d : kd.apps.DaemonSet) (gr : GR) (rv : GoString)
    (h : s1Ok σ M Lm C Ld) (hd : dsAtOwner σ o = some d)
    (hLd : dsSeenBy σ o Ld) :
    s1Ok σ (wroteAtM M o d.ObjectMeta'.UID' gr rv) Lm C Ld := by
  refine ⟨h.s1, h.scene, ?_, h.claimDs, ?_⟩
  · intro o' d' hd'
    refine ownerOk_wroteAt σ M _ C o o' _ _ gr rv (h.owners o' d' hd') ?_
    intro e; subst e; rw [hd] at hd'; cases hd'; rfl
  · intro o' r hr
    by_cases e : o = o'
    · subst e; exact ⟨by rw [hd]; rfl, hLd⟩
    · unfold wroteAtM at hr
      rw [GMap.lookup_insert_ne _ _ e] at hr
      exact h.recDs o' r hr

/-- **The claimant's `WroteAt`** of its pod's version `rvStr c`, for the owner and its
DaemonSet's UID: the record covers the pod, the claim is written. -/
theorem wrote_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld : Nat) (o : Owner) (d : kd.apps.DaemonSet) (n : GoString) (k : Key) (c : w64)
    (h : s1Ok σ M Lm C Ld) (hd : dsAtOwner σ o = some d)
    (hC : C !! (o, n) = some (some (false, k, c.toNat))) (hc : 1 ≤ c.toNat)
    (hLd : dsSeenBy σ o Ld) :
    s1Ok σ (wroteAtM M o d.ObjectMeta'.UID' podGR (rvStr c)) Lm
      (<[(o, n) := some (true, k, c.toNat)]> C) Ld := by
  have h1 := wroteAt_step σ M Lm C Ld o d podGR (rvStr c) h hd hLd
  have hP : ∀ o', pendOf (<[(o, n) := some (true, k, c.toNat)]> C) o' = pendOf C o' := by
    intro o'; funext k' c'; exact propext (pendOf_write C o o' n k k' c.toNat c' hC)
  refine ⟨h1.s1, h1.scene, ?_, ?_, h1.recDs⟩
  · intro o' d' hd'
    have ho := h1.owners o' d' hd'
    refine ⟨(by rw [hP]; exact ho.acct),
      (fun hr => (readyAcct_congr _ _ _ _ _ _ (fun k c => by rw [hP])).2 (ho.ready hr)),
      ho.recok, ?_, ?_⟩
    · intro n' v hC' k' p hk hon
      simp only [GMap.lookup_insert_eq_iff] at hC'
      split at hC'
      · rename_i e
        obtain ⟨w, c', hv, hc'⟩ := ho.claims n' _ (by rw [← e]; exact hC) k' p hk hon
        simp only [Option.some.injEq] at hC'
        subst hC'
        simp only [Option.some.injEq, Prod.mk.injEq] at hv
        obtain ⟨-, rfl, rfl⟩ := hv
        exact ⟨true, c.toNat, rfl, hc'⟩
      · exact ho.claims n' v hC' k' p hk hon
    · intro n' k' c' hC'
      simp only [GMap.lookup_insert_eq_iff] at hC'
      split at hC'
      · rename_i e
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        simp only [Option.some.injEq, Prod.mk.injEq] at hC'
        obtain ⟨-, rfl, rfl⟩ := hC'
        have hwf : vsWf (recFor M o d.ObjectMeta'.UID').vs := by
          have ho0 := h.owners o d hd
          unfold recFor
          split
          · rename_i r hr
            split
            · exact (ho0.recok r hr).2
            · intro gr x hx; simp at hx
          · intro gr x hx; simp at hx
        exact recCovers_wroteAt_new M o _ (rvStr c) _ hwf (wellFormed_rvStr c hc)
          (by rw [decVal_rvStr]; exact Nat.le_refl _)
      · exact ho.wrote n' k' c' hC'
  · intro o' n' v hC'
    simp only [GMap.lookup_insert_eq_iff] at hC'
    split at hC'
    · rename_i e
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      rw [hd]; rfl
    · exact h1.claimDs o' n' v hC'

/-- **A written claim released** (by the sync, after its creates): the owner is no longer ready. -/
theorem release_step (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld : Nat) (o : Owner) (n : GoString) (k : Key) (c : Nat) (h : s1Ok σ M Lm C Ld)
    (hC : C !! (o, n) = some (some (true, k, c))) :
    s1Ok σ M (<[o := ((lbOf Lm o).1, false)]> Lm) (GMap.delete (o, n) C) Ld := by
  refine ⟨h.s1, h.scene, ?_, ?_, h.recDs⟩
  · intro o' d' hd'
    have ho := h.owners o' d' hd'
    have hlb : (lbOf (<[o := ((lbOf Lm o).1, false)]> Lm) o').1 = (lbOf Lm o').1 := by
      by_cases e : o = o'
      · subst e; rw [lbOf_insert_eq]
      · rw [lbOf_insert_ne _ _ e]
    have hpend : ∀ k' c', pendOf (GMap.delete (o, n) C) o' k' c' → pendOf C o' k' c' := by
      rintro k' c' ⟨n', w, h'⟩
      simp only [GMap.lookup_delete_iff] at h'
      split at h'
      · cases h'
      · exact ⟨n', w, h'⟩
    refine ⟨?_, ?_, ho.recok, ?_, ?_⟩
    · rw [hlb]
      intro k' p hk hu
      obtain ⟨c', hc', hcase⟩ := ho.acct k' p hk hu
      refine ⟨c', hc', ?_⟩
      rcases hcase with h1 | h2 | ⟨n', w, h3⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
      · by_cases e : (o, n) = (o', n')
        · simp only [Prod.mk.injEq] at e
          obtain ⟨rfl, rfl⟩ := e
          rw [hC] at h3
          simp only [Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨rfl, rfl, rfl⟩ := h3
          exact Or.inr (Or.inl (ho.wrote n _ _ hC))
        · exact Or.inr (Or.inr ⟨n', w, by
            simp only [GMap.lookup_delete_iff, e, ↓reduceIte]; exact h3⟩)
    · intro hr
      by_cases e : o = o'
      · subst e; rw [lbOf_insert_eq] at hr; cases hr
      · rw [lbOf_insert_ne _ _ e] at hr ⊢
        intro k' p hk hu
        obtain ⟨c', hc', hcase⟩ := ho.ready hr k' p hk hu
        refine ⟨c', hc', ?_⟩
        rcases hcase with h1 | ⟨n', w, h3⟩
        · exact Or.inl h1
        · refine Or.inr ⟨n', w, ?_⟩
          have e' : (o, n) ≠ (o', n') := by
            intro ee; simp only [Prod.mk.injEq] at ee; exact e ee.1
          simp only [GMap.lookup_delete_iff, e', ↓reduceIte]; exact h3
    · intro n' v hC' k' p hk hon
      simp only [GMap.lookup_delete_iff] at hC'
      split at hC'
      · cases hC'
      · exact ho.claims n' v hC' k' p hk hon
    · intro n' k' c' hC'
      simp only [GMap.lookup_delete_iff] at hC'
      split at hC'
      · cases hC'
      · exact ho.wrote n' k' c' hC'
  · intro o' n' v hC'
    simp only [GMap.lookup_delete_iff] at hC'
    split at hC'
    · cases hC'
    · exact h.claimDs o' n' v hC'

/-- **`Clear(o, uid)` changes nothing** for an owner with no DaemonSet, or whose DaemonSet's UID is
not a non-empty `uid` (`deleteDaemonset`'s, for a DaemonSet that is gone: the record, if any, is
the stored DaemonSet's, `recOk`; and a missing DaemonSet has none, `recDs`). -/
theorem clear_noop (σ : St) (M : GMap Owner consistency.Rec) (Lm : GMap Owner (Nat × Bool))
    (C : Claims) (Ld : Nat) (o : Owner) (uid : GoString) (h : s1Ok σ M Lm C Ld)
    (hgone : dsAtOwner σ o = none ∨
      (uid ≠ [] ∧ ∀ d, dsAtOwner σ o = some d → d.ObjectMeta'.UID' ≠ uid)) :
    clearM M o uid = M := by
  unfold clearM
  split
  · rename_i r hr
    obtain ⟨hs, -⟩ := h.recDs o r hr
    rcases hgone with hn | ⟨hu, hne⟩
    · rw [hn] at hs; cases hs
    · cases hdo : dsAtOwner σ o with
      | none => rw [hdo] at hs; cases hs
      | some d =>
        have hruid := ((h.owners o d hdo).recok r hr).1
        rw [ite_eq_right_iff.mpr (fun hc => absurd hc ?_)]
        rintro (h1 | h2)
        · exact hu h1
        · exact hne d hdo (hruid ▸ h2)
  · rfl

/-- **`Clear(o, uid)` changes nothing** when every logged change of the owner's DaemonSet is after
`Ld` (`syncDaemonSet`'s `Clear` on `NotFound`: its DaemonSet cache, at a version at least `Ld`,
does not show it; a record would be of a DaemonSet seen by `Ld`, `recDs`). -/
theorem clear_notfound_noop (σ : St) (M : GMap Owner consistency.Rec)
    (Lm : GMap Owner (Nat × Bool)) (C : Claims) (Ld : Nat) (o : Owner) (uid : GoString)
    (h : s1Ok σ M Lm C Ld) (hnf : ∀ c ∈ σ.dss.log, c.obj.key = o → Ld < c.rv.toNat) :
    clearM M o uid = M := by
  unfold clearM
  split
  · rename_i r hr
    obtain ⟨-, c, hc, hk, hcl⟩ := h.recDs o r hr
    exact absurd hcl (Nat.not_le.mpr (hnf c hc hk))
  · rfl

end pure

end dsctl
end EtcdGrove
end Perennial
