/-
**What `lessor.initAndRecover` makes** (the lease-expiry plan's S1, 2026-11-04): the leases it
recovers from the `Lease` bucket's records, before they join the lessor (`Recover`). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.MustUnsafeGetAllLeases

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI

/-- **The lease map of the recovered leases** `xs` (each a record `(id, ttl, rem)` with its
`*Lease`), inserted in order into `m` (`le.leaseMap[ID] = &Lease{...}`). -/
def recMapFrom (m : GMap w64 Loc) (xs : List ((w64 × w64 × w64) × Loc)) : GMap w64 Loc :=
  xs.foldl (fun m p => m.insert p.1.1 p.2) m

/-- The lease map of the recovered leases, from an empty map. -/
abbrev recMap (xs : List ((w64 × w64 × w64) × Loc)) : GMap w64 Loc := recMapFrom ∅ xs

/-- **The TTLs of the recovered leases** (`lpb.TTL` raised to the minimum `mt`). -/
def recTTLsFrom (mt : w64) (m : GMap w64 w64) (xs : List (w64 × w64 × w64)) : GMap w64 w64 :=
  xs.foldl (fun m x => m.insert x.1 (grantTTL mt x.2.1)) m

/-- The TTLs of the recovered leases, from an empty map. -/
abbrev recTTLs (mt : w64) (xs : List (w64 × w64 × w64)) : GMap w64 w64 := recTTLsFrom mt ∅ xs

/-! ### Maps built by inserting a list's elements in order (`recMapFrom`, `recTTLsFrom`) -/

section fold
variable {α K V : Type} [DecidableEq K]

/-- An insertion of a key no later element has commutes to the end. -/
theorem foldIns_out (f : α → K) (g : α → V) (k : K) (v : V) :
    ∀ (xs : List α) (m : GMap K V), k ∉ xs.map f →
      xs.foldl (fun m x => m.insert (f x) (g x)) (m.insert k v) =
        (xs.foldl (fun m x => m.insert (f x) (g x)) m).insert k v
  | [], _, _ => rfl
  | y :: ys, m, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.foldl_cons]
    rw [GMap.insert_commute m (g y) v (Ne.symm h.1)]
    exact foldIns_out f g k v ys _ h.2

/-- The first element's insertion, last (its key not among the others'). -/
theorem foldIns_cons (f : α → K) (g : α → V) (x : α) (xs : List α) (m : GMap K V)
    (h : f x ∉ xs.map f) :
    (x :: xs).foldl (fun m x => m.insert (f x) (g x)) m =
      (xs.foldl (fun m x => m.insert (f x) (g x)) m).insert (f x) (g x) := by
  rw [List.foldl_cons]; exact foldIns_out f g (f x) (g x) xs m h

/-- The keys of the built map: the list's and the initial map's. -/
theorem foldIns_isSome (f : α → K) (g : α → V) (k : K) :
    ∀ (xs : List α) (m : GMap K V),
      ((xs.foldl (fun m x => m.insert (f x) (g x)) m).lookup k).isSome ↔
        k ∈ xs.map f ∨ (m.lookup k).isSome
  | [], m => by simp
  | y :: ys, m => by
    rw [List.foldl_cons, foldIns_isSome f g k ys, GMap.lookup_insert_is_Some]
    simp only [List.map_cons, List.mem_cons]
    by_cases hk : f y = k
    · subst hk; simp
    · have hk' : ¬ k = f y := fun h => hk h.symm
      simp [hk, hk']

/-- The values of the built map, its keys distinct. -/
theorem foldIns_lookup (f : α → K) (g : α → V) (k : K) (v : V) :
    ∀ (xs : List α) (m : GMap K V), (xs.map f).Nodup →
      ((xs.foldl (fun m x => m.insert (f x) (g x)) m).lookup k = some v ↔
        (∃ x ∈ xs, f x = k ∧ g x = v) ∨ (k ∉ xs.map f ∧ m.lookup k = some v))
  | [], m, _ => by simp
  | y :: ys, m, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [foldIns_cons f g y ys m hnd.1, GMap.lookup_insert_Some, foldIns_lookup f g k v ys m hnd.2]
    simp only [List.mem_cons, List.map_cons, exists_eq_or_imp, not_or]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨hne, h | ⟨h1, h2⟩⟩)
      · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨⟨fun h => hne h.symm, h1⟩, h2⟩
    · rintro ((⟨rfl, rfl⟩ | ⟨x, hx, rfl, rfl⟩) | ⟨⟨h1, h2⟩, h3⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · refine Or.inr ⟨fun h => hnd.1 ?_, Or.inl ⟨x, hx, rfl, rfl⟩⟩
        rw [h]; exact List.mem_map_of_mem hx
      · exact Or.inr ⟨fun h => h1 h.symm, Or.inr ⟨h2, h3⟩⟩

/-- The built map is no larger than the initial map and the list together. -/
theorem foldIns_size (f : α → K) (g : α → V) :
    ∀ (xs : List α) (m : GMap K V),
      GMap.size (xs.foldl (fun m x => m.insert (f x) (g x)) m) ≤ GMap.size m + xs.length
  | [], _ => by simp
  | y :: ys, m => by
    rw [List.foldl_cons]
    have h1 := foldIns_size f g ys (m.insert (f y) (g y))
    have h2 := GMap.map_size_insert m (f y) (g y)
    simp only [List.length_cons]
    split at h2 <;> omega

end fold

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A lease `initAndRecover` made** at `l`, from the record `x = (id, ttl, rem)` by a lessor
whose minimum TTL is `mt`: its fields, owned whole (as `NewLease` leaves them, `Grant`'s TTL
raise done): the id, the TTL `grantTTL mt ttl`, the remaining TTL `rem`, its two locks unlocked,
`expiry` the zero time (`forever`), an empty item set and a fresh `revokec` with the right to close
it. -/
def recLease (mt : w64) (x : w64 × w64 × w64) (l : Loc) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ lsF go!"ID" l ↦ x.1 ∗ lsF go!"ttl" l ↦ grantTTL mt x.2.1 ∗
    lsF go!"remainingTTL" l ↦ x.2.2 ∗
    lsF go!"expiryMu" l ↦ (zero_val _root_.Perennial.sync.RWMutex) ∗
    lsF go!"expiry" l ↦ (zero_val _root_.Perennial.time.Time) ∗
    lsF go!"mu" l ↦ (zero_val _root_.Perennial.sync.RWMutex) ∗
    (∃ sm : Loc, lsF go!"itemSet" l ↦ sm ∗ sm ↦$ (∅ : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem Unit)) ∗
    (∃ c : GoChan, lsF go!"revokec" l ↦ c ∗ revokeCloser c))

end defs

end lease
end EtcdGrove
end Perennial
