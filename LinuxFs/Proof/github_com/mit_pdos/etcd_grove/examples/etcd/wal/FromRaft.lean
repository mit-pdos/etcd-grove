/-
Lean-first (no Rocq counterpart).

# `fromRaft`, transliterated (W4c U5)

`fromRaft(re)` (`examples/etcd/wal/wal.go`) reads an entry back from the model `m` of the `*raftpb.Entry`:
the index, the term, the data's length and its first 8 bytes as the salt (`tFromRaftE`); the size is set
to 0 when the data is not `entData` of those (`tFromRaft`). `tFromRaft_absEnt`: a tester entry reads
back as itself.
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- `fromRaft`'s salt loop's step at byte `i`. -/
def tSaltStep (d : List w8) (s : w64) (i : Nat) : w64 :=
  s ||| (W64 (uint.Z (d[i]?.getD (W8 0))) <<< (W64 8 * W64 (i : Int)))

/-- `fromRaft`'s salt: the first (at most) 8 bytes, little-endian. -/
def tSaltOf (d : List w8) : w64 := (List.range (min 8 d.length)).foldl (tSaltStep d) (W64 0)

/-- `fromRaft`'s entry before the check. -/
def tFromRaftE (m : EntryM) : TEnt := ⟨m.Index', m.Term', W64 (m.Data'.length : Int), tSaltOf m.Data'⟩

/-- `fromRaft`: the entry, its size 0 unless the data is `entData` of it. -/
def tFromRaft (m : EntryM) : TEnt :=
  open Classical in
  if m.Data' = tEntData (tFromRaftE m) then tFromRaftE m else { tFromRaftE m with size' := W64 0 }

theorem take_succ_eq_iff {α : Type} {a b : List α} {i : Nat} {x y : α} (ha : a[i]? = some x)
    (hb : b[i]? = some y) : a.take (i + 1) = b.take (i + 1) ↔ (a.take i = b.take i ∧ x = y) := by
  rw [List.take_add_one, List.take_add_one, ha, hb]
  simp only [Option.toList_some]
  constructor
  · intro h
    have hl : (a.take i).length = (b.take i).length := by
      have h1 := (List.getElem?_eq_some_iff.1 ha).1; have h2 := (List.getElem?_eq_some_iff.1 hb).1
      simp; omega
    obtain ⟨h1, h2⟩ := List.append_inj h hl
    exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, rfl⟩; rw [h1]

theorem tEntData_prefix8 (e : TEnt) (h8 : 8 ≤ uint.nat e.size') (i : Nat) (hi : i < 8) :
    (tEntData e)[i]? = some (W8 (uint.Z (e.salt' >>> W64 (8 * (i : Int))))) := by
  unfold tEntData
  rw [List.getElem?_append_left (by simp; omega)]
  simp [Nat.min_eq_left h8, hi]

theorem tEntData_len (e : TEnt) : (tEntData e).length = uint.nat e.size' := by
  unfold tEntData; simp; omega

theorem tSaltOf_tEntData (e : TEnt) (h8 : 8 ≤ uint.nat e.size') : tSaltOf (tEntData e) = e.salt' := by
  unfold tSaltOf
  rw [tEntData_len, Nat.min_eq_left h8]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil, tSaltStep]
  simp only [tEntData_prefix8 e h8 _ (by decide : (0:Nat) < 8), tEntData_prefix8 e h8 _ (by decide : (1:Nat) < 8),
    tEntData_prefix8 e h8 _ (by decide : (2:Nat) < 8), tEntData_prefix8 e h8 _ (by decide : (3:Nat) < 8),
    tEntData_prefix8 e h8 _ (by decide : (4:Nat) < 8), tEntData_prefix8 e h8 _ (by decide : (5:Nat) < 8),
    tEntData_prefix8 e h8 _ (by decide : (6:Nat) < 8), tEntData_prefix8 e h8 _ (by decide : (7:Nat) < 8),
    Option.getD_some]
  generalize e.salt' = x
  have hb : ∀ y : w64, W64 (uint.Z (W8 (uint.Z y))) = BitVec.zeroExtend 64 (BitVec.truncate 8 y) := by
    intro y; apply BitVec.eq_of_toNat_eq; simp [uint.Z]; omega
  simp only [hb]
  push_cast
  simp only [Int.reduceMul, BitVec.ofInt_ofNat]
  bv_decide

/-- **A tester entry reads back as itself.** -/
theorem tFromRaft_absEnt (e : TEnt) (h8 : 8 ≤ uint.nat e.size') : tFromRaft (absEnt e) = e := by
  have hE : tFromRaftE (absEnt e) = e := by
    unfold tFromRaftE absEnt
    simp only
    rw [tSaltOf_tEntData e h8, tEntData_len]
    cases e; simp only; congr 1; word
  unfold tFromRaft
  rw [hE]
  simp [absEnt]

end pure

end etcd_wal
end EtcdGrove
end Perennial
