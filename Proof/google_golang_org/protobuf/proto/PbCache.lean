/-
**protobuf-go's size cache, as the protobuf model keeps it** (#37 stage S3; the design: etcd-grove #37,
"S3 design: protobuf-go's size cache", decisions D-A, D-B, D-C). Every message level has a
`sizeCache int32`: the model's `PbModelSize` (protobuf-go's `sizePointer`, `internal/impl/encode.go:
47-132`) stores the level's size plus one into it, atomically (0 past `MaxInt32 - 1`: `cacheStore`);
under `UseCachedSize` a level whose cache is above 0 is not recomputed but read (the cache minus one),
and a nested level's cached size is the length prefix `PbModelAppend` checks the bytes against (a
mismatch fails the marshal: D-C, no error post, ruled out by premises only).

**The cache modes** (`PbCacheMode`), what a spec knows of a level's cache:
- `any`: nothing (D-B: a fractionally shared message that is not frozen; or a frozen one whose caches
  are in an invariant that says nothing of them, as `walpb.Record`'s `recHidden`). A cached size
  of such a level is any value; an uncached one is the size.
- `excl`: the owner holds the cache (its points-to), so it knows each level's value: after an
  uncached `PbModelSize`, `cacheStore` of the size (`cacheStore_fresh`).
- `frozen n`: a frozen message of size `n` whose every cache, once written, is 0 or `n + 1`
  (`cacheFresh`): every write is a recomputation from frozen fields, hence of the same value; the
  mode D-A needs for a default `Marshal`, which reads the nested caches.

**`nestedFresh`**: every nested level's cache is fresh (the premise of a cached marshal of a message
with message fields). At a type without message fields (`walpb.Record`) the list of nested levels is
empty and the premise holds (`nestedFresh_nil`): its cached marshal's bytes never read a cache.

This first version has what `walpb.Record`'s methods use (the mode `any`) and the definitions the
general case is stated in; the modes' ghost state (an `excl` level's points-to, a `frozen` level's
invariant) comes with the first type with message fields.
-/
module

public import Perennial.Proof.ProofPrelude

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- What a spec knows of a message level's size cache (see the file header). -/
inductive PbCacheMode where
  | any
  | excl
  | frozen (n : Nat)

/-- **What a recomputing `PbModelSize` stores** for a level of size `n` (`encode.go:118-130`): the
size plus one, or 0 if that does not fit an `int32`. -/
def cacheStore (n : Nat) : w32 := if n > 2147483646 then W32 0 else W32 ((n + 1 : Nat) : Int)

/-- **A fresh cache** of a level of size `n`: never written (0, or a 0 stored past `MaxInt32 - 1`),
or the size plus one. A cached read of a fresh cache above 0 is the size. -/
def cacheFresh (n : Nat) (sc : w32) : Prop := sc = W32 0 ∨ uint.nat sc = n + 1

/-- What the mode says of a level of size `n` whose cache holds `sc`. -/
def PbCacheMode.holds : PbCacheMode → Nat → w32 → Prop
  | .any, _, _ => True
  | .excl, n, sc => cacheFresh n sc
  | .frozen m, n, sc => m = n ∧ cacheFresh n sc

/-- **Every nested level's cache is fresh** (each level: its size and its cache). -/
def nestedFresh (levels : List (Nat × w32)) : Prop := ∀ p ∈ levels, cacheFresh p.1 p.2

theorem cacheStore_fresh (n : Nat) : cacheFresh n (cacheStore n) := by
  unfold cacheStore cacheFresh
  split
  · left; rfl
  · right; word

/-- A message without message fields has no nested level. -/
theorem nestedFresh_nil : nestedFresh [] := by
  intro p hp; cases hp

end EtcdGrove
end Perennial
