/-
FNV-1a 64 (`hash/fnv`'s `New64a`, `(*sum64a).Write`, `(*sum64a).Sum64`), as a pure function:
the offset basis, then for each byte `c`, `hash ^= sum64a(c); hash *= prime64` (`fnv.go`). The
specs of `Spec/hash/fnv/` are stated over it. Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Std.Word

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace hash.fnv

/-- `offset64`, FNV-64's offset basis. -/
def fnv64aOffset : w64 := W64 14695981039346656037

/-- `prime64`, FNV-64's prime. -/
def fnv64aPrime : w64 := W64 1099511628211

/-- One byte of FNV-1a 64: `hash ^= sum64a(c); hash *= prime64`. -/
def fnv64aStep (h : w64) (c : w8) : w64 := (h ^^^ c.zeroExtend 64) * fnv64aPrime

/-- FNV-1a 64 of `bs` from the state `h` (`Write(bs)` on a `sum64a` holding `h`). -/
def fnv64aFrom (h : w64) (bs : List w8) : w64 := bs.foldl fnv64aStep h

/-- **FNV-1a 64** of `bs` (`New64a()`, `Write(bs)`, `Sum64()`). -/
def fnv64a (bs : List w8) : w64 := fnv64aFrom fnv64aOffset bs

theorem fnv64aFrom_nil (h : w64) : fnv64aFrom h [] = h := rfl

theorem fnv64aFrom_append (h : w64) (as bs : List w8) :
    fnv64aFrom h (as ++ bs) = fnv64aFrom (fnv64aFrom h as) bs :=
  List.foldl_append

end hash.fnv
end EtcdGrove
end Perennial
