/-
The hraft kit's clients' commands (notes/dsv-hraft.md, S5f): the bytes `opID(c, seq)` and
`command(c, seq, x)` build (`opIDB`, `cmdB`), and what the kit's state at the frontier reads of
them (`KitQ.lean`): the id `idOf (cmdB c s x) = (c, s)` for `c < 256`, `s < 2 ^ 56` (`idOf_cmdB`),
and the datum is the command of its input (`datumOf_cmdB`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.KitQ

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet

section pure
variable [GooseExts]

/-- `x`'s eight bytes, big-endian, as `opID`'s loop stores them (`b[i] = byte(x >> (56 - 8*i))`). -/
def beBytes (x : w64) : List w8 :=
  (List.range 8).map (fun (i : Nat) => W8 (uint.Z (x >>> (W64 56 - W64 8 * W64 (i : Int)))))

/-- The word `opID(c, seq)` encodes: `c` in the top byte, `seq` below. -/
def opIDW (c s : w64) : w64 := (c <<< W64 56) ||| (s % W64 72057594037927936)

/-- `opID(c, seq)`'s bytes. -/
def opIDB (c s : w64) : List w8 := beBytes (opIDW c s)

/-- `command(c, seq, x)`'s bytes: the kind (`CmdPut`, 80, or `CmdGet`, 71), the id, a put's value. -/
def cmdB (c s : w64) (put : Bool) (v : GoString) : List w8 :=
  if put then W8 80 :: opIDB c s ++ v else W8 71 :: opIDB c s

theorem beBytes_length (x : w64) : (beBytes x).length = 8 := by simp [beBytes]

theorem beBytes_getElem (x j : w64) (hj : uint.nat j < 8) :
    (beBytes x)[uint.nat j]? = some (W8 (uint.Z (x >>> (W64 56 - W64 8 * j)))) := by
  unfold beBytes
  rw [List.getElem?_map, List.getElem?_range hj]
  simp only [Option.map_some]
  congr
  word

theorem opIDB_length (c s : w64) : (opIDB c s).length = 8 := beBytes_length _

theorem opIDW_toNat (c s : w64) (hc : uint.nat c < 256) :
    uint.nat (opIDW c s) = uint.nat c * 2 ^ 56 + uint.nat s % 2 ^ 56 := by
  unfold opIDW
  simp only [uint.nat, uint.Z, Int.toNat_natCast]
  rw [BitVec.shiftLeft_eq', BitVec.toNat_or, BitVec.toNat_umod, BitVec.toNat_shiftLeft]
  have h56 : (W64 56 : w64).toNat = 56 := rfl
  have hm : (W64 72057594037927936 : w64).toNat = 2 ^ 56 := rfl
  rw [h56, hm, Nat.shiftLeft_eq]
  have hc' : c.toNat < 256 := by simpa [uint.nat, uint.Z] using hc
  rw [Nat.mod_eq_of_lt (by omega : c.toNat * 2 ^ 56 < 2 ^ 64), Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by decide)), Nat.mul_comm]

/-- The bytes read back, as `idOf` reads them. -/
theorem beBytes_fold (x : w64) :
    (beBytes x).foldl (fun a b => a * 256 + uint.nat b) 0 = uint.nat x := by
  have hx : uint.nat x < 2 ^ 64 := by have := x.isLt; simpa [uint.nat, uint.Z] using this
  have hb : ∀ k : Nat, k < 8 → uint.nat (W8 (uint.Z (x >>> (W64 56 - W64 8 * W64 (k : Int))))) =
      uint.nat x / 2 ^ (56 - 8 * k) % 256 := by
    intro k hk
    have hk' : (W64 56 - W64 8 * W64 (k : Int) : w64).toNat = 56 - 8 * k := by
      rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | rfl | omega
    simp only [uint.nat, uint.Z, Int.toNat_natCast, W8, BitVec.toNat_ofInt, BitVec.ushiftRight_eq',
      BitVec.toNat_ushiftRight, hk', Nat.shiftRight_eq_div_pow]
    omega
  simp only [beBytes, List.range_succ, List.range_zero, List.nil_append, List.map_append,
    List.map_cons, List.map_nil, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), hb 3 (by omega), hb 4 (by omega),
    hb 5 (by omega), hb 6 (by omega), hb 7 (by omega)]
  simp only [Nat.reduceMul, Nat.reduceSub, Nat.reducePow]
  omega

/-- **A command's id** is its client's and its count's. -/
theorem idOf_cmdB (c s : w64) (put : Bool) (v : GoString) (hc : uint.nat c < 256) :
    idOf (cmdB c s put v) = (uint.nat c, uint.nat s % 2 ^ 56) := by
  have h8 : ((opIDB c s ++ (if put then v else [])).take 8) = opIDB c s := by
    rw [List.take_append_of_le_length (by simp [opIDB_length]),
      List.take_of_length_le (by simp [opIDB_length])]
  have hd : (cmdB c s put v).drop 1 = opIDB c s ++ (if put then v else []) := by
    unfold cmdB; cases put <;> simp
  unfold idOf
  simp only
  rw [hd, h8]
  unfold opIDB
  rw [beBytes_fold, opIDW_toNat c s hc]
  have hlt : uint.nat s % 2 ^ 56 < 2 ^ 56 := Nat.mod_lt _ (by decide)
  ext
  · simp only; omega
  · simp only; omega

/-- **A command is the datum of its input**: a put iff the input is, with its value. -/
theorem datumOf_cmdB (c s : w64) (i : HIn) :
    datumOf i (cmdB c s i.1.1 i.1.2.2) := by
  unfold datumOf cmdB service.isPut service.putVal
  cases hp : i.1.1
  · refine ⟨⟨fun h => ?_, fun h => by cases h⟩, fun h => by cases h⟩
    have h2 := h.2
    simp at h2
  · refine ⟨⟨fun _ => rfl, fun _ => ⟨by simp [opIDB_length], rfl⟩⟩, fun _ => ?_⟩
    rw [if_pos rfl, List.cons_append, show (9 : Nat) = 8 + 1 from rfl, List.drop_succ_cons, List.drop_left' (opIDB_length c s)]

end pure

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
