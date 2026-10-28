/-
**S1, `MaxOnePodPerNode`, as a pure model** (phase 5 of `notes/k8s-daemonset-plan.md`, first
round). Lean-first (no Rocq counterpart).

* `targetNode K Op d`: `util.GetTargetNodeName(pod)` (`daemon/util/daemonset_util.go:225`) on the
  pod's deep value: its `Spec.NodeName` if set, else the single value of the first
  `MatchFields` requirement with key `K` and operator `Op` of the required node affinity's terms
  (`K`, `Op` the values of `metav1.ObjectNameField` and `v1.NodeSelectorOpIn`, names-only
  constants of the pinned translation; `none` for the function's errors).
* `ctlBy u d`: an owner reference of the pod with UID `u` and `Controller` set (`dsmain`'s
  `controlledBy`).
* `S1 K Op σ u`: no two stored pods controlled by `u` target one node (`dsmain`'s checker, over
  every namespace).

**The accounting invariant** (`acct`): every stored pod controlled by `u` was added (the latest
`ADDED` change at its key, `addedRv`) at a version that is (a) at most `L`, a version the pod
informer's store has reached for good (the Iris side holds `infRvLb` of it), or (b) at most the
version the consistency store records for the DaemonSet's owner and the pods' group resource
(`recCovers`), or (c) pending: created by the sync that holds the owner's token and not yet
accounted for (`P`). At a sync's start no pod is pending; `EnsureReady` succeeding turns (b) into
(a) (`acct_ensureReady`); a create commits a pending pod (`acct_create`); the sync's `WroteAt` of
the created pod's version turns it into (b) (`acct_wroteAt`).

**Where it breaks** (`ambiguous_create_breaks_S1`): a create that commits and returns the model's
timeout (`writeRet`'s ambiguous branch, `Config.AmbiguousWrites`) leaves the pod pending with no
version to record: `RealPodControl.createPods` returns before `OnWrite`
(`controller_utils.go:618`). The next sync's `EnsureReady` has nothing to wait for, its pod cache
may still be at the version before the create, and it creates a second pod on the node:
`issues/k8s-daemonset-ambiguous-create-duplicate-pod.md`, reached by the model's own operations
(`CreateOut`, the informer contract's `View.ok`, `EnsureReady` on an absent record).
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open apimodel informer consistency resourceversion

section model
variable [FfiSyntax]

/-! ## The target node, the owner, S1 -/

/-- `metav1.ObjectNameField` (a translated constant since phase 5). -/
def keyName : GoString := go!"metadata.name"
/-- `v1.NodeSelectorOpIn` (a translated constant since phase 5). -/
def opIn : GoString := go!"In"

/-- The first `MatchFields` requirement with key `K` and operator `Op` of the terms, in order
(`GetTargetNodeName`'s loop). -/
def nameReq (K Op : GoString) : List kd.core.NodeSelectorTerm → Option kd.core.NodeSelectorRequirement
  | [] => none
  | t :: ts =>
    match t.MatchFields'.find? (fun e => decide (e.Key' = K ∧ e.Operator' = Op)) with
    | some e => some e
    | none => nameReq K Op ts

/-- The required node affinity's terms, if any. -/
def reqTerms (d : kd.core.Pod) : Option (List kd.core.NodeSelectorTerm) :=
  match d.Spec'.Affinity' with
  | none => none
  | some a => match a.NodeAffinity' with
    | none => none
    | some na => match na.RequiredDuringSchedulingIgnoredDuringExecution' with
      | none => none
      | some ns => some ns.NodeSelectorTerms'

/-- **`util.GetTargetNodeName(pod)`**: `some n` for the node name it returns, `none` for its
errors. -/
def targetNode (K Op : GoString) (d : kd.core.Pod) : Option GoString :=
  if d.Spec'.NodeName' ≠ go!"" then some d.Spec'.NodeName' else
  match reqTerms d with
  | none => none
  | some ts => match nameReq K Op ts with
    | none => none
    | some e => match e.Values' with
      | [v] => some v
      | _ => none

/-- **The pod is controlled by `u`** (`dsmain`'s `controlledBy`). -/
def ctlBy (u : GoString) (d : kd.core.Pod) : Prop :=
  ∃ r ∈ d.ObjectMeta'.OwnerReferences', r.UID' = u ∧ r.Controller' = some true

/-- **A pod of the DaemonSet `u` on node `n`.** -/
def dsPodOn (K Op u n : GoString) : Obj → Prop
  | .pod d => ctlBy u d ∧ targetNode K Op d = some n
  | _ => False

/-- **S1, `MaxOnePodPerNode`**: no two stored pods of the DaemonSet `u` target one node. -/
def S1 (K Op : GoString) (σ : St) (u : GoString) : Prop :=
  ∀ k1 k2 o1 o2 n, σ.pods.objs !! k1 = some o1 → σ.pods.objs !! k2 = some o2 →
    dsPodOn K Op u n o1 → dsPodOn K Op u n o2 → k1 = k2

/-- **A pod of `u`.** -/
def dsPod (u : GoString) : Obj → Prop
  | .pod d => ctlBy u d
  | _ => False

theorem dsPodOn_dsPod {K Op u n : GoString} {o : Obj} (h : dsPodOn K Op u n o) : dsPod u o := by
  cases o <;> simp_all [dsPodOn, dsPod]

/-! ## The accounting invariant -/

/-- The version of the latest `ADDED` change at key `k` (the current incarnation's creation). -/
def addedRv (l : List Change) (k : Key) : Option Nat :=
  (l.filter (fun c => decide (c.typ = .added ∧ c.obj.key = k))).getLast?.map (fun c => c.rv.toNat)

/-- The pods' group resource. -/
def podGR : GR := ⟨go!"", go!"pods"⟩

/-- **The consistency store's record covers version `c`**: it records, for the pods, a
well-formed version at least `c`. -/
def recCovers (rc : Option consistency.Rec) (c : Nat) : Prop :=
  ∃ r w, rc = some r ∧ r.vs !! podGR = some w ∧ wellFormed w = true ∧ c ≤ decVal w

/-- **The accounting invariant** of the DaemonSet `u` (see the file header): each of its stored
pods was added at a version seen by the informer for good (`≤ L`), or covered by the owner's
record, or is pending. -/
def acct (σ : St) (u : GoString) (L : Nat) (rc : Option consistency.Rec) (P : List Key) : Prop :=
  ∀ k o, σ.pods.objs !! k = some o → dsPod u o →
    ∃ c, addedRv σ.pods.log k = some c ∧ (c ≤ L ∨ recCovers rc c ∨ k ∈ P)

/-- What `EnsureReady` succeeding gives for the pods (`readyRec`, with the store's contract
`G podGR readRV`: the store has reached `decVal readRV`, which is well formed): the recorded
version is at most the store's. -/
def readyPods (rc : Option consistency.Rec) (L' : Nat) : Prop :=
  ∀ r w, rc = some r → r.vs !! podGR = some w → wellFormed w = true → decVal w ≤ L'

/-- **`EnsureReady` succeeding**: the record goes, and every pod it covered is now at most the
store's version `L'` (`L ≤ L'`: the bound only grows). -/
theorem acct_ensureReady (σ : St) (u : GoString) (L L' : Nat) (rc : Option consistency.Rec) (P : List Key)
    (h : acct σ u L rc P) (hL : L ≤ L') (hr : readyPods rc L') : acct σ u L' none P := by
  intro k o hk hu
  obtain ⟨c, hc, hcase⟩ := h k o hk hu
  refine ⟨c, hc, ?_⟩
  rcases hcase with h1 | ⟨r, w, hrec, hw, hwf, hcw⟩ | h3
  · exact Or.inl (Nat.le_trans h1 hL)
  · exact Or.inl (Nat.le_trans hcw (hr r w hrec hw hwf))
  · exact Or.inr (Or.inr h3)

/-- With nothing pending and no record, every pod of `u` was added at a version the informer has
reached (`≤ L`). -/
theorem acct_seen (σ : St) (u : GoString) (L : Nat) (h : acct σ u L none []) :
    ∀ k o, σ.pods.objs !! k = some o → dsPod u o → ∃ c, addedRv σ.pods.log k = some c ∧ c ≤ L := by
  intro k o hk hu
  obtain ⟨c, hc, hcase⟩ := h k o hk hu
  rcases hcase with h1 | ⟨r, w, hrec, -⟩ | h3
  · exact ⟨c, hc, h1⟩
  · cases hrec
  · cases h3

/-- **The record only grows**: `WroteAt` raises the pods' version (`wroteAtVs`); a pod covered
before is covered after. -/
theorem recCovers_wroteAt (M : GMap Owner consistency.Rec) (o : Owner) (uid : GoString) (gr : GR)
    (rv : GoString) (c : Nat) (huid : ∀ r, M !! o = some r → r.uid = uid)
    (h : recCovers (M !! o) c) : recCovers ((wroteAtM M o uid gr rv) !! o) c := by
  obtain ⟨r, w, hrec, hw, hwf, hcw⟩ := h
  have hfor : recFor M o uid = r := by
    unfold recFor; rw [hrec]; simp [huid r hrec]
  unfold wroteAtM
  simp only [GMap.lookup_insert_eq]
  rw [hfor]
  unfold wroteAtVs
  by_cases hwr : wellFormed rv = true
  · simp only [hwr, ↓reduceIte]
    by_cases hg : gr = podGR
    · subst hg
      rw [hw]
      by_cases hlt : decVal w < decVal rv
      · simp only [hlt, ↓reduceIte]
        exact ⟨_, rv, rfl, by simp, hwr, by omega⟩
      · simp only [hlt, ↓reduceIte]
        exact ⟨_, w, rfl, hw, hwf, hcw⟩
    · split
      · exact ⟨_, w, rfl, by rw [GMap.lookup_insert_ne _ _ hg]; exact hw, hwf, hcw⟩
      · split
        · exact ⟨_, w, rfl, by rw [GMap.lookup_insert_ne _ _ hg]; exact hw, hwf, hcw⟩
        · exact ⟨_, w, rfl, hw, hwf, hcw⟩
  · simp only [hwr, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, w, rfl, hw, hwf, hcw⟩

/-- **`WroteAt` of the created pod's version accounts for it**: after
`WroteAt(o, uid, podGR, rv)` with `rv` well formed, the record covers every version up to
`decVal rv` (the record's versions are well formed, `vsWf`, as the store keeps them). -/
theorem recCovers_wroteAt_new (M : GMap Owner consistency.Rec) (o : Owner) (uid : GoString) (rv : GoString)
    (c : Nat) (hwfR : vsWf (recFor M o uid).vs) (hwf : wellFormed rv = true)
    (hc : c ≤ decVal rv) : recCovers ((wroteAtM M o uid podGR rv) !! o) c := by
  unfold wroteAtM
  simp only [GMap.lookup_insert_eq]
  unfold wroteAtVs
  simp only [hwf, ↓reduceIte]
  split
  · exact ⟨_, rv, rfl, by simp, hwf, hc⟩
  · rename_i old hold
    by_cases hlt : decVal old < decVal rv
    · simp only [hlt, ↓reduceIte]
      exact ⟨_, rv, rfl, by simp, hwf, hc⟩
    · simp only [hlt, ↓reduceIte]
      exact ⟨_, old, rfl, hold, hwfR _ _ hold, by omega⟩

/-! ## A create keeps the pod's owner and target -/

/-- **The pod `syncNodes` asks to create for node `n`**: no name, a generated name (the
DaemonSet's, `getPodsPrefix`), no version, no namespace (`GetPodFromTemplate`), the DaemonSet's
controller reference, the node's affinity (`ReplaceDaemonSetPodNodeNameNodeAffinity`), so it
targets `n`. -/
structure newPodOk (K Op u n : GoString) (d : kd.core.Pod) : Prop where
  ctl : ctlBy u d
  tgt : targetNode K Op d = some n
  noName : d.ObjectMeta'.Name' = go!""
  gen : d.ObjectMeta'.GenerateName' ≠ go!""
  noRv : d.ObjectMeta'.ResourceVersion' = go!""
  noNs : d.ObjectMeta'.Namespace' = go!""

/-- The pod's create strategy keeps its node name and affinity. -/
theorem preparePodD_spec (d : kd.core.Pod) :
    (preparePodD d).Spec'.NodeName' = d.Spec'.NodeName' ∧
    (preparePodD d).Spec'.Affinity' = d.Spec'.Affinity' ∧
    (preparePodD d).ObjectMeta'.OwnerReferences' = d.ObjectMeta'.OwnerReferences' := by
  simp [preparePodD]

theorem targetNode_congr (K Op : GoString) (d d' : kd.core.Pod)
    (h1 : d'.Spec'.NodeName' = d.Spec'.NodeName') (h2 : d'.Spec'.Affinity' = d.Spec'.Affinity') :
    targetNode K Op d' = targetNode K Op d := by
  unfold targetNode reqTerms
  rw [h1, h2]

/-- **The created pod** (`createApply` of a pod): its key, and it is of `u` on `n` if the request
was. -/
theorem createApply_pod (K Op u n ns : GoString) (d : kd.core.Pod) (σ : St)
    (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) (h : newPodOk K Op u n d) :
    (createApply .pods ns (.pod d) σ t).1.key =
      mkKey ns (d.ObjectMeta'.GenerateName' ++ rvStr (σ.rev + 1)) ∧
    dsPodOn K Op u n (createApply .pods ns (.pod d) σ t).1 := by
  obtain ⟨⟨r, hr, hu, hc⟩, htg, hnm, -, -, hns⟩ := h
  simp only [createApply, createNs, Res.namespaced, ↓reduceIte, Obj.meta, hns, Obj.modMeta,
    Obj.setMeta, prepareD, hnm]
  refine ⟨by simp [Obj.key, Obj.meta, preparePodD], ?_, ?_⟩
  · refine ⟨r, ?_, hu, hc⟩
    simpa [preparePodD] using hr
  · rw [← htg]
    apply targetNode_congr <;> simp [preparePodD]

/-- The empty server is well formed (as `NewServer`'s proof shows). -/
theorem St.empty_wf' : St.empty.wf := by
  refine ⟨by simp [St.empty], ?_, ?_, ?_, ?_, by simp [St.empty], ?_⟩ <;>
    first
    | (intro r; cases r <;> simp [St.empty, St.tbl, replay])
    | (intro r c hc; cases r <;> simp [St.empty, St.tbl] at hc)

theorem decStr_ne {m n : w64} (h : m ≠ n) : decStr m ≠ decStr n := fun e => h (decStr_inj e)

/-! ## The ambiguous create breaks S1 -/

/-- **An ambiguous pod create breaks S1**, through the model's own operations (the execution of
`issues/k8s-daemonset-ambiguous-create-duplicate-pod.md`, from the empty server):

1. a sync creates the pod for node `n`: the create commits (`CreateOut`, `ok (true, o1)`) and,
   with `AmbiguousWrites` (`mayHappen true false`: the flag on, the controller's client not an
   admin's), returns the timeout instead (`writeRet`'s second branch: the result pointer `nil`,
   so no resource version reaches `OnWrite`, and `createPods` returns before it). The consistency
   store records nothing for the owner, and the pod is not accounted for: `acct` holds only with
   it pending;
2. the pod informer's store may still be at the version before the create (`View.ok` against the
   new log: the informer contract allows it, its version only bounded by the server's);
3. the next sync's `EnsureReady` finds no record (it succeeds, `readyRec _ _ none`), its cache has
   no pod of `u` on `n`, and its create commits too: two pods of `u` on `n`, `¬ S1`. -/
theorem ambiguous_create_breaks_S1 (K Op u n ns : GoString) (d : kd.core.Pod) (fail : Bool)
    (h : newPodOk K Op u n d) (t1 t2 : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) :
    let σ0 := St.empty
    let o1 := (createApply .pods ns (.pod d) σ0 t1).1
    let σ1 := (createApply .pods ns (.pod d) σ0 t1).2
    let o2 := (createApply .pods ns (.pod d) σ1 t2).1
    let σ2 := (createApply .pods ns (.pod d) σ1 t2).2
    σ0.wf ∧ S1 K Op σ0 u ∧
    -- (1) the create commits and may report the timeout; the pod is left pending
    CreateOut fail false .pods ns (.pod d) σ0 (.ok (true, o1)) σ1 ∧ mayHappen true false ∧
    acct σ1 u σ0.rev.toNat none [o1.key] ∧ ¬ acct σ1 u σ0.rev.toNat none [] ∧
    -- (2) the pod informer's store may still be at the version before it, with no pod of `u`
    View.ok σ1.pods.log ⟨∅, some σ0.rev.toNat⟩ ∧
    -- (3) the next sync's create commits: two pods of `u` on `n`
    CreateOut fail false .pods ns (.pod d) σ1 (.ok (true, o2)) σ2 ∧ ¬ S1 K Op σ2 u := by
  intro σ0 o1 σ1 o2 σ2
  obtain ⟨hk1, hp1⟩ := createApply_pod K Op u n ns d σ0 t1 h
  obtain ⟨hk2, hp2⟩ := createApply_pod K Op u n ns d σ1 t2 h
  have hrev0 : σ0.rev = W64 1 := rfl
  have hrev1 : σ1.rev = W64 2 := by simp [σ1, σ0, createApply, St.empty]
  -- the two names differ: their suffixes are the decimal forms of 2 and 3
  have hkey : o1.key ≠ o2.key := by
    simp only [o1, o2] at hk1 hk2 ⊢
    rw [hk1, hk2, hrev0, hrev1]
    intro e
    simp only [mkKey, k8s_io.apimachinery.pkg.types.NamespacedName.mk.injEq, true_and,
      List.append_cancel_left_eq] at e
    exact decStr_ne (by decide) e
  have hobjs1 : σ1.pods.objs = <[o1.key := o1]> ∅ := by
    simp [σ1, o1, σ0, createApply, St.setTbl, St.tbl, St.empty]
  have hlog1 : σ1.pods.log = [⟨.added, W64 2, o1⟩] := by
    simp [σ1, o1, σ0, createApply, St.setTbl, St.tbl, St.empty]
  have hobjs2 : σ2.pods.objs = <[o2.key := o2]> (<[o1.key := o1]> ∅) := by
    simp only [σ2, o2, createApply, St.setTbl, St.tbl]
    rw [← hobjs1]
  refine ⟨St.empty_wf', ?_, ?_, ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro k1 k2 o1' o2' n' h1
    simp [σ0, St.empty] at h1
  · refine Or.inr (Or.inr ⟨?_, ⟨t1, rfl, rfl⟩⟩)
    simp [createErr, σ0, St.empty, St.tbl, createNs, Res.namespaced, Obj.modMeta, Obj.setMeta,
      Obj.meta, h.noRv, h.noName, h.gen, h.noNs]
  · intro k o hk hu
    rw [hobjs1] at hk
    by_cases hk' : o1.key = k
    · subst hk'
      refine ⟨2, ?_, Or.inr (Or.inr (by simp))⟩
      rw [hlog1]; simp [addedRv]
    · simp [hk'] at hk
  · intro hacc
    obtain ⟨c, hc, hcase⟩ := hacc o1.key o1 (by rw [hobjs1]; simp) (dsPodOn_dsPod hp1)
    rw [hlog1] at hc
    simp [addedRv] at hc
    subst hc
    rcases hcase with h1 | ⟨r, -, hr, -⟩ | h3
    · simp [σ0, St.empty] at h1
    · cases hr
    · cases h3
  · show (∅ : GMap Key Obj) = tableAt σ1.pods.log σ0.rev.toNat
    rw [hlog1]
    simp [tableAt, replay, σ0, St.empty]
  · refine Or.inr (Or.inr ⟨?_, ⟨t2, rfl, rfl⟩⟩)
    have hfresh : ((σ1.tbl .pods).objs !! mkKey ns
        (d.ObjectMeta'.GenerateName' ++ rvStr (σ1.rev + 1))).isSome = false := by
      show (σ1.pods.objs !! _).isSome = false
      rw [hobjs1, hk1]
      simp only [GMap.lookup_insert_eq_iff]
      rw [if_neg]
      · simp
      · rw [hrev0, hrev1]
        intro e
        simp only [mkKey, k8s_io.apimachinery.pkg.types.NamespacedName.mk.injEq, true_and,
          List.append_cancel_left_eq] at e
        exact decStr_ne (by decide) e
    simp only [createErr, createNs, Res.namespaced, ↓reduceIte, Obj.modMeta, Obj.setMeta,
      Obj.meta, h.noRv, h.noName, h.noNs]
    simp only [h.gen, false_and, ↓reduceIte]; simpa using hfresh
  · intro hs
    exact hkey (hs o1.key o2.key o1 o2 n (by rw [hobjs2]; simp [Ne.symm hkey])
      (by rw [hobjs2]; simp) hp1 hp2)

end model

end dsctl
end EtcdGrove
end Perennial
