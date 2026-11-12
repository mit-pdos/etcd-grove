/-
Lean-first (no Rocq counterpart).

# The store's history, kept by its caller (D30j's local option)

The store's specs read etcd's key-values through `kvSeen γh σ` (`Store.lean`): the ghost map `γh`
holds, read-only, each revision's changes (`Changes`: the keys it wrote, with `some` of the value,
and the keys it deleted, with `none`), and every key-value of the state is among the changes of
its mod revision. The caller that hands the store its updates keeps the map's authority with
etcd's state (`histAuth γh σ`): every entry at a revision at most the state's (`HistOk`), and the
state seen. At each step of etcd's state that the updates report (`KvNext`, `Updates.lean`), it
adds the step's changes (`chgOf σ σ'`) at the new revision, where nothing was (`histAuth_next`),
and the entry comes back (`revSeen`): a deleted object's witness (stage 7b), and, for every other
key, the proof that the revision did not change it.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Updates

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

open Classical in
/-- **The changes of a step from `σ` to `σ'`**: the key-values of `σ'` not in `σ` (`some` of the
value), then the keys of `σ` that `σ'` lacks (`none`). -/
def chgOf (σ σ' : KVState) : Changes :=
  (σ'.kvs.filter (fun v => decide (v ∉ σ.kvs))).map (fun v => (v.key, some v.value)) ++
  ((σ.kvs.filter (fun v => decide (∀ w ∈ σ'.kvs, w.key ≠ v.key))).map EtcdKv.key).map
    (fun k => (k, (none : Option GoString)))

open Classical in
/-- A new key-value is among the changes. -/
theorem chgOf_new (σ σ' : KVState) (v : EtcdKv) (h1 : v ∈ σ'.kvs) (h2 : v ∉ σ.kvs) :
    (v.key, some v.value) ∈ chgOf σ σ' :=
  List.mem_append_left _ (List.mem_map.2 ⟨v, List.mem_filter.2 ⟨h1, by simpa using h2⟩, rfl⟩)

open Classical in
/-- A deleted key is among the changes, with `none`. -/
theorem chgOf_del (σ σ' : KVState) (k : GoString) (h1 : ∃ v ∈ σ.kvs, v.key = k)
    (h2 : ∀ v ∈ σ'.kvs, v.key ≠ k) : (k, (none : Option GoString)) ∈ chgOf σ σ' := by
  obtain ⟨v, hv, rfl⟩ := h1
  refine List.mem_append_right _ (List.mem_map.2 ⟨v.key, List.mem_map.2 ⟨v,
    List.mem_filter.2 ⟨hv, ?_⟩, rfl⟩, rfl⟩)
  simpa using h2

open Classical in
/-- **A key the step did not change**: a key among the changes has a new key-value in `σ'` or
was deleted. -/
theorem chgOf_keys (σ σ' : KVState) (k : GoString) (x : Option GoString)
    (h : (k, x) ∈ chgOf σ σ') :
    (∃ v ∈ σ'.kvs, v ∉ σ.kvs ∧ v.key = k) ∨ ((∃ v ∈ σ.kvs, v.key = k) ∧ ∀ v ∈ σ'.kvs, v.key ≠ k) := by
  simp only [chgOf, List.mem_append, List.map_map, List.mem_map, List.mem_filter,
    Function.comp_def, Prod.mk.injEq] at h
  rcases h with ⟨v, ⟨hv, hn⟩, rfl, -⟩ | ⟨v, ⟨hv, hd⟩, rfl, -⟩
  · exact Or.inl ⟨v, hv, by simpa using hn, rfl⟩
  · exact Or.inr ⟨⟨v, hv, rfl⟩, by simpa using hd⟩

open Classical in
/-- The changes of a step between sorted states have distinct keys. -/
theorem chgOf_nodup (σ σ' : KVState) (hs0 : σ.kvs.Pairwise etcdKvLess)
    (hs : σ'.kvs.Pairwise etcdKvLess) : ((chgOf σ σ').map Prod.fst).Nodup := by
  have hp' : (σ'.kvs.map EtcdKv.key).Nodup := by
    have hp : (σ'.kvs.map EtcdKv.key).Pairwise go.GoStringLt := List.pairwise_map.2 hs
    exact hp.imp (fun h e => by subst e; exact go.goStringLt_irrefl _ h)
  have hp0 : (σ.kvs.map EtcdKv.key).Nodup := by
    have hp : (σ.kvs.map EtcdKv.key).Pairwise go.GoStringLt := List.pairwise_map.2 hs0
    exact hp.imp (fun h e => by subst e; exact go.goStringLt_irrefl _ h)
  unfold chgOf
  rw [List.map_append, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_map]
    exact hp'.sublist (List.filter_sublist.map _)
  · rw [List.map_map, List.map_map]
    exact hp0.sublist (List.filter_sublist.map _)
  · intro a ha b hb hab
    simp only [List.map_map, List.mem_map, List.mem_filter, Function.comp_def] at ha hb
    obtain ⟨v, ⟨hv, -⟩, rfl⟩ := ha
    obtain ⟨w, ⟨-, hw⟩, rfl⟩ := hb
    exact (of_decide_eq_true hw) v hv hab

/-- The history's entries are at revisions at most the state's. -/
def HistOk (H : GMap w64 Changes) (σ : KVState) : Prop :=
  ∀ r ch, H !! r = some ch → uint.nat r ≤ σ.rev

/-- **The history's authority at etcd's state `σ`** (see the file header). -/
def histAuth (γh : GName) (σ : KVState) : IProp GF :=
  iprop(∃ H, ghostMapAuth γh 1 H ∗ ⌜HistOk H σ⌝ ∗ kvSeen γh σ)

instance histAuth_timeless (γh : GName) (σ : KVState) : Timeless (histAuth (GF := GF) γh σ) := by
  unfold histAuth kvSeen; infer_instance

/-- The state, seen. -/
theorem histAuth_seen (γh : GName) (σ : KVState) :
    histAuth (GF := GF) γh σ ⊢ histAuth γh σ ∗ kvSeen γh σ := by
  iintro H
  iunfold histAuth at H
  icases H with ⟨%H, HA, %Hok, #Hs⟩
  iframe Hs
  iunfold histAuth
  iexists H
  iframe HA Hs
  ipureintro; exact Hok

/-- **The step from `σ` to `σ'`, recorded** (persistent): when `σ'` is at the next revision, its
changes are the history's entry there. -/
def revSeen (γh : GName) (σ σ' : KVState) : IProp GF :=
  iprop(□ (⌜σ'.rev = σ.rev + 1⌝ → ghostMapElem γh (W64 ((σ'.rev : Nat) : Int)) DFrac.discard
    (chgOf σ σ')))

instance revSeen_persistent (γh : GName) (σ σ' : KVState) :
    Persistent (revSeen (GF := GF) γh σ σ') := by
  unfold revSeen; infer_instance

/-- **The history follows a step of etcd's state** (see the file header): both states sorted
(distinct keys), the new revision fitting a word; the step's entry comes back. -/
theorem histAuth_next (γh : GName) (σ σ' : KVState) (hn : KvNext σ σ') (hr : σ'.rev < 2 ^ 64)
    (hs0 : σ.kvs.Pairwise etcdKvLess) (hs : σ'.kvs.Pairwise etcdKvLess) :
    histAuth (GF := GF) γh σ ⊢ |==> (histAuth γh σ' ∗ revSeen γh σ σ') := by
  rcases hn with rfl | ⟨hrev, hnew⟩
  · iintro H
    imodintro
    iframe H
    iunfold revSeen
    imodintro
    iintro %hk
    exfalso; omega
  iintro H
  iunfold histAuth at H
  icases H with ⟨%H, HA, %Hok, #Hs⟩
  have hR : uint.nat (W64 ((σ'.rev : Nat) : Int)) = σ'.rev := by
    simp only [W64, uint.nat, BitVec.toNat_ofInt]; omega
  have hfr : H !! W64 ((σ'.rev : Nat) : Int) = none := by
    cases h : H !! W64 ((σ'.rev : Nat) : Int) with
    | none => rfl
    | some x =>
      have := Hok _ _ h
      omega
  have hnd := chgOf_nodup σ σ' hs0 hs
  imod ghost_map_insert_persist (W64 ((σ'.rev : Nat) : Int)) (chgOf σ σ') hfr $$ HA
    with ⟨HA, #He⟩
  imodintro
  isplitl [HA]
  · iunfold histAuth
    iexists (H.insert (W64 ((σ'.rev : Nat) : Int)) (chgOf σ σ'))
    iframe HA
    isplitr
    · ipureintro
      intro r ch hv
      by_cases e : W64 ((σ'.rev : Nat) : Int) = r
      · subst e; omega
      · rw [GMap.lookup_insert_ne _ _ e] at hv
        have := Hok _ _ hv; omega
    iunfold kvSeen
    imodintro
    iintro %v %hv
    by_cases hin : v ∈ σ.kvs
    · iunfold kvSeen at Hs
      iapply Hs
      ipureintro; exact hin
    · have hm : v.modRev = W64 ((σ'.rev : Nat) : Int) := by
        rcases hnew v hv with h | h
        · exact absurd h hin
        · exact h
      iexists (chgOf σ σ')
      rw [hm]
      iframe He
      ipureintro
      exact ⟨chgOf_new σ σ' v hv hin, hnd⟩
  · iunfold revSeen
    imodintro
    iintro %-
    iexact He

end defs

end k8s
end EtcdGrove
end Perennial
