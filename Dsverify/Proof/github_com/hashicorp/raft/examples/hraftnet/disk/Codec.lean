/-
(hraft_robust R3) The disk's file encoding (`codec.go`), as pure functions: unsigned integers as 8 bytes,
little-endian (`encU64`); byte strings length-prefixed (`encBytes`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Base

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet.disk

/-- `putUint64`'s bytes: `x`'s eight bytes, least significant first. -/
def encU64 (x : w64) : List w8 := (List.range 8).map (fun i : Nat => W8 (uint.Z (x >>> W64 (8 * (i : Int)))))

theorem encU64_length (x : w64) : (encU64 x).length = 8 := by simp [encU64]

theorem encU64_take_succ (x : w64) (i : Nat) (hi : i < 8) :
    (encU64 x).take (i + 1) = (encU64 x).take i ++ [W8 (uint.Z (x >>> W64 (8 * (i : Int))))] := by
  unfold encU64
  rw [List.take_add_one, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- `putBytes`'s bytes: the length, then the bytes. -/
def encBytes (s : List w8) : List w8 := encU64 (W64 s.length) ++ s

end github_com.hashicorp.raft.examples.hraftnet.disk

end Perennial
