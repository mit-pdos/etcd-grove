/-
`runner.checkLeases`' model facts (mvccrand's `WriterLease.lean` over the keys `ks`): the history's
state at the member's revision matches the store's state after its log (`hist_rev_match`); `GetLease`
of a key is the tester's lease of it (`leaseGet_eq`); the keys the store's item map puts on a live
lease are the tester's keys on it in order (`leaseDelKeys_eq_onLease`), among `ks`
(`leaseKeys_sub`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Writer
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LeaseItems

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

/-- **The tester's lease of a key** in the map `M` (`0` for none). -/
def leaseOfM (M : GMap GoString kvRec) (k : GoString) : w64 :=
  match M !! k with
  | some e => e.lease'
  | none => W64 0

/-- **The history's revision at the member's revision matches the store's state after its log.** -/
theorem hist_rev_match (ks : List GoString) (hks : ks.Pairwise go.GoStringLt) (ops : List OpM)
    (h : logOk ks ops) (n : Nat) (hn : n ≤ ops.length) :
    ∃ e, (histAt ks ops n)[revAfter ks ops n]? = some e ∧
      stMatch ks e.1 (stateAfter (σOf ks ops n).log) := by
  obtain ⟨-, ⟨hl, hr⟩, -⟩ := logOk_hist ks hks ops h n n (Nat.le_refl _) hn
  have hlen : (σOf ks ops n).log.length = (histAt ks ops n).length := by
    simp [σOf, logOfHist_length]
  have h2 : 2 ≤ (histAt ks ops n).length := by
    have := (runM_inv ks ops h n).1.length_le
    simp [hist0] at this; unfold histAt; omega
  have hrv : revAfter ks ops n = (σOf ks ops n).log.length - 1 := by
    rw [hlen]; unfold revAfter MSt.rev histAt; rfl
  rw [σOf_notified] at hl hr
  obtain ⟨e, he, hst, -⟩ := hr ((σOf ks ops n).log.length - 1) (by omega)
  refine ⟨e, by rw [hrv]; exact he, ?_⟩
  rw [← mvcc.stateAt_last]; exact hst

/-- **`GetLease` of a key is the tester's lease of it** (the store's item map of a state the map
`M` matches). -/
theorem leaseGet_eq (ks : List GoString) (M : GMap GoString kvRec) (s : List EtcdKv)
    (hM : stMatch ks M s) (k : GoString) :
    ((leaseItemsOf s).lookup (go_etcd_io.etcd.server.v3.lease.LeaseItem.mk k)).getD (W64 0) =
      leaseOfM M k := by
  rw [leaseItemsOf_lookup]
  simp only
  rw [hM.1 k]
  unfold leaseOfM
  cases M !! k with
  | none => rfl
  | some e =>
    simp only [Option.map_some, Option.bind_some, kvLease, kvOfRec]
    by_cases h : e.lease' = W64 0
    · simp [h]
    · have h' : (e.lease' = W64 0) = False := eq_false h
      simp only [h', ↓reduceIte]; rfl

/-- **The keys the store's item map puts on a live lease `id` (not `0`) are the tester's keys on
it, in its order.** -/
theorem leaseDelKeys_eq_onLease (ks : List GoString) (hks : ks.Pairwise go.GoStringLt)
    (M : GMap GoString kvRec) (s : List EtcdKv) (hM : stMatch ks M s)
    (hs : s.Pairwise etcdKvLess) (id : w64) (hid : id ≠ W64 0) :
    leaseDelKeys s id = ks.filter (onLease M id) := by
  apply eq_of_lt_sorted_mem (leaseDelKeys_sorted hs id) (hks.filter _)
  intro x
  rw [leaseDelKeys_mem hs id x, leaseItemsOf_lookup, List.mem_filter]
  simp only
  rw [hM.1 x]
  unfold onLease
  cases hx : M !! x with
  | none => simp
  | some e =>
    simp only [Option.map_some, Option.bind_some, kvLease, kvOfRec, decide_eq_true_eq]
    have hk : x ∈ ks := by
      have hf := hM.1 x
      rw [hx] at hf
      have hm := List.mem_of_find?_eq_some hf
      have hkk := findKey_key hf
      simp only [kvOfRec] at hkk
      have := hM.2 _ hm
      simp only [kvOfRec] at this
      exact this
    by_cases h : e.lease' = W64 0
    · simp only [h, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      intro _ h'; exact hid h'.symm
    · simp only [h, ↓reduceIte, Option.some.injEq, hk, true_and]

/-- The keys the store's item map puts on `id` are among the tester's keys. -/
theorem leaseKeys_sub (ks : List GoString) (M : GMap GoString kvRec) (s : List EtcdKv)
    (hM : stMatch ks M s) (id : w64) (k : GoString)
    (h : (leaseItemsOf s).lookup (go_etcd_io.etcd.server.v3.lease.LeaseItem.mk k) = some id) :
    k ∈ ks := by
  rw [leaseItemsOf_lookup] at h
  simp only at h
  cases hf : findKey k s with
  | none => rw [hf] at h; cases h
  | some kv =>
    have := hM.2 kv (List.mem_of_find?_eq_some hf)
    rwa [findKey_key hf] at this

end model

end mvccfull
end EtcdGrove
end Perennial
