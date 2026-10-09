/-
A `for k, v := range m` loop whose body changes the map it ranges over, at the current key
only (deletes it, or assigns to it), as the demux does (`broadcastProgressLocked`,
`broadcastEventsLocked`, `resyncLaggingWatchers`: `delete(d.activeWatchers, w)`,
`d.activeWatchers[w] = ...`, `d.laggingWatchers[w] = ...` inside `for w, nextRev := range
d.activeWatchers` / `d.laggingWatchers`). Go allows this: "If a map entry that has not yet
been reached is removed during iteration, the corresponding iteration value will not be
produced"; an entry already reached may be changed or deleted freely.

**Perennial gap: `wp_map_for_range_mut_keys` is false in Perennial's current Go semantics,
and is the one `sorry` of the demux** (`wp_map_for_range_mut` is derived from it). `map.forRange` (`Perennial/Golang/Defn/Map.lean`) does
`StartRead m`, iterates over the value read, then `FinishRead m`: the map's location stays in
the `Reading 1` state for the whole loop, and a `map.insert`/`go.delete` on it in the body
(`PrepareWrite`, which needs `Reading 0`) is stuck. So Perennial's model treats a write to a
map during its own iteration as a data race, which Go's single-goroutine semantics does not.
The statement below is what Go guarantees for a body that only touches the current key: the
keys are those of the map when the loop starts (each once), the value passed for a key is
the one it had then, and the body owns the map and may change the current key. It would be
provable for a Go-faithful `forRange` that reads the domain once (`StartRead`/`FinishRead`
around the domain), then, for each key, looks it up at that point and skips it if it is
gone (Go's rule for deleted entries; entries inserted during the loop may be skipped, which
Go allows). The fix belongs in Perennial (`map.forRange` and `wp_map_for_range`).
-/
module

public import Perennial.Golang.Theory.Map

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section forRangeMut
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]

/-- `for k, v := range m { body }` where the body owns the map (full ownership, `mref ↦$`)
and changes at most the current key: called on the `i`-th key `key` of the domain `keys`
(the map's keys at the start, each once) with the value `v` it had at the start, when the
map is `m'` (equal to `m` on the keys not yet visited), it returns the map as `m''`, equal
to `m'` except at `key`. `P keys i m'` is the loop invariant (it may mention the order of
the keys, as `wp_map_for_range`'s does). A `break`/`return` of the body must establish `Φ`
itself (the body holds the map).

**Perennial gap** (see the module docstring): false in Perennial's present semantics of
`map.forRange`; Go's semantics makes it true. -/
theorem wp_map_for_range_mut_keys (P : List K → Nat → GMap K V → IProp GF) (body : GoFunc)
    (key_type elem_type : go.GoType) (mref : Loc) (m : GMap K V)
    [TypedPointsto (GF := GF) K] [IntoValTyped (GF := GF) K key_type] (Φ : val → IProp GF) :
    (mref ↦$ m : IProp GF) -∗
    (∀ keys : List K,
      ⌜(∀ k, k ∈ keys ↔ (m !! k).isSome) ∧ keys.length = GMap.size m ∧ keys.Nodup⌝ -∗
      (P keys 0 m ∗
       □ (∀ (i : Nat) (key : K) (v : V) (m' : GMap K V),
          ⌜keys[i]? = some key ∧ m !! key = some v ∧
            ∀ (j : Nat) (k : K), i ≤ j → keys[j]? = some k → m' !! k = m !! k⌝ -∗
          P keys i m' -∗ mref ↦$ m' -∗
          WP (App (App (Val #body) (Val #key)) (Val #v))
            {{ bv, forMapPostcondition
                iprop(∃ m'' : GMap K V, mref ↦$ m'' ∗ P keys (i + 1) m'' ∗
                  ⌜∀ k, k ≠ key → m'' !! k = m' !! k⌝) Φ bv }}) ∗
       (∀ m' : GMap K V, P keys keys.length m' -∗ mref ↦$ m' -∗ Φ executeVal))) -∗
    WP (App (App (Val (map.forRange key_type elem_type)) (Val #mref)) (Val #body)) {{ Φ }} := by
  sorry

/-- `wp_map_for_range_mut_keys` with an invariant that does not mention the keys. -/
theorem wp_map_for_range_mut (P : Nat → GMap K V → IProp GF) (body : GoFunc)
    (key_type elem_type : go.GoType) (mref : Loc) (m : GMap K V)
    [TypedPointsto (GF := GF) K] [IntoValTyped (GF := GF) K key_type] (Φ : val → IProp GF) :
    (mref ↦$ m : IProp GF) -∗
    (∀ keys : List K,
      ⌜(∀ k, k ∈ keys ↔ (m !! k).isSome) ∧ keys.length = GMap.size m ∧ keys.Nodup⌝ -∗
      (P 0 m ∗
       □ (∀ (i : Nat) (key : K) (v : V) (m' : GMap K V),
          ⌜keys[i]? = some key ∧ m !! key = some v ∧
            ∀ (j : Nat) (k : K), i ≤ j → keys[j]? = some k → m' !! k = m !! k⌝ -∗
          P i m' -∗ mref ↦$ m' -∗
          WP (App (App (Val #body) (Val #key)) (Val #v))
            {{ bv, forMapPostcondition
                iprop(∃ m'' : GMap K V, mref ↦$ m'' ∗ P (i + 1) m'' ∗
                  ⌜∀ k, k ≠ key → m'' !! k = m' !! k⌝) Φ bv }}) ∗
       (∀ m' : GMap K V, P keys.length m' -∗ mref ↦$ m' -∗ Φ executeVal))) -∗
    WP (App (App (Val (map.forRange key_type elem_type)) (Val #mref)) (Val #body)) {{ Φ }} := by
  iintro Hm H
  iapply wp_map_for_range_mut_keys (fun _ i m' => P i m') body key_type elem_type mref m Φ
    $$ Hm H

end forRangeMut

end EtcdGrove
end Perennial
