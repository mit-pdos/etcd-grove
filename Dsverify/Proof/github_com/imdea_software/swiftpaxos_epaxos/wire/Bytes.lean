/-
Byte buffers of the generated marshalers (internal to the wire package): a local `[n]byte` array
sliced as `b[:n]`, and the bytes `byte(x >> k)` of an integer stored one by one.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.WProg
public import Perennial.Proof.encoding.binary.Results

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem w64_succ (j : Nat) : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by
  unfold W64
  rw [show ((j + 1 : Nat) : Int) = (j : Int) + 1 by omega, BitVec.ofInt_add]

theorem w8_sint {n : Nat} (y : BitVec n) (hn : 8 ≤ n) : W8 (sint.Z y) = y.setWidth 8 := by
  have : W8 (sint.Z y) = y.signExtend 8 := rfl
  rw [this, BitVec.signExtend_eq_setWidth_of_le _ hn]

theorem w8_uint {n : Nat} (y : BitVec n) : W8 (uint.Z y) = y.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq; simp [W8, uint.Z]

/-- The low byte of an arithmetic shift by `k` (`k + 8 ≤ n`) is the logical shift's: no sign bit
reaches it (replaces a `bv_decide`, which would add `Lean.ofReduceBool` to the trust base). -/
theorem sshift_low8 {n : Nat} (x : BitVec n) (y : BitVec 64) (hk : y.toNat + 8 ≤ n) :
    (BitVec.sshiftRight' x y).setWidth 8 = (x >>> y).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 : ¬ n ≤ i := by omega
  have h2 : y.toNat + i < n := by omega
  simp [BitVec.sshiftRight', BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, hi,
    BitVec.getLsbD_sshiftRight, h1, h2]

/-- The bytes `byte(x)`, `byte(x >> 8)`, ... of an `int32` (arithmetic shifts). -/
theorem u32Le_sbytes (x : w32) :
    [W8 (sint.Z x), W8 (sint.Z (BitVec.sshiftRight' x (W64 8))),
      W8 (sint.Z (BitVec.sshiftRight' x (W64 16))), W8 (sint.Z (BitVec.sshiftRight' x (W64 24)))]
      = u32Le x := by
  rw [encoding.binary.u32Le_4]
  simp only [w8_sint _ (by decide : 8 ≤ 32), w8_uint, List.cons.injEq, and_true]
  refine ⟨trivial, ?_, ?_, ?_⟩ <;> exact sshift_low8 _ _ (by decide)

/-- The bytes `byte(x)`, `byte(x >> 8)`, ... of an `int64` (arithmetic shifts). -/
theorem u64Le_sbytes (x : w64) :
    [W8 (sint.Z x), W8 (sint.Z (BitVec.sshiftRight' x (W64 8))),
      W8 (sint.Z (BitVec.sshiftRight' x (W64 16))), W8 (sint.Z (BitVec.sshiftRight' x (W64 24))),
      W8 (sint.Z (BitVec.sshiftRight' x (W64 32))), W8 (sint.Z (BitVec.sshiftRight' x (W64 40))),
      W8 (sint.Z (BitVec.sshiftRight' x (W64 48))), W8 (sint.Z (BitVec.sshiftRight' x (W64 56)))]
      = u64Le x := by
  rw [encoding.binary.u64Le_8]
  simp only [w8_sint _ (by decide : 8 ≤ 64), w8_uint, List.cons.injEq, and_true]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact sshift_low8 _ _ (by decide)

theorem u32Le_sbytes_cons (x : w32) (l : List w8) :
    W8 (sint.Z x) :: W8 (sint.Z (BitVec.sshiftRight' x (W64 8))) ::
      W8 (sint.Z (BitVec.sshiftRight' x (W64 16))) ::
      W8 (sint.Z (BitVec.sshiftRight' x (W64 24))) :: l = u32Le x ++ l := by
  rw [← u32Le_sbytes]; rfl

theorem u64Le_sbytes_cons (x : w64) (l : List w8) :
    W8 (sint.Z x) :: W8 (sint.Z (BitVec.sshiftRight' x (W64 8))) ::
      W8 (sint.Z (BitVec.sshiftRight' x (W64 16))) :: W8 (sint.Z (BitVec.sshiftRight' x (W64 24))) ::
      W8 (sint.Z (BitVec.sshiftRight' x (W64 32))) :: W8 (sint.Z (BitVec.sshiftRight' x (W64 40))) ::
      W8 (sint.Z (BitVec.sshiftRight' x (W64 48))) ::
      W8 (sint.Z (BitVec.sshiftRight' x (W64 56))) :: l = u64Le x ++ l := by
  rw [← u64Le_sbytes]; rfl

theorem set_all8 {α} (L : List α) (h : L.length = 8) (a0 a1 a2 a3 a4 a5 a6 a7 : α) :
    ((((((((L.set 0 a0).set 1 a1).set 2 a2).set 3 a3).set 4 a4).set 5 a5).set 6 a6).set 7 a7) =
      [a0, a1, a2, a3, a4, a5, a6, a7] := by
  match L, h with
  | [_, _, _, _, _, _, _, _], _ => rfl

theorem set_all4 {α} (L : List α) (h : L.length = 4) (a0 a1 a2 a3 : α) :
    ((((L.set 0 a0).set 1 a1).set 2 a2).set 3 a3) = [a0, a1, a2, a3] := by
  match L, h with
  | [_, _, _, _], _ => rfl

set_option hygiene false in
/-- Normalize the stored bytes in `Hbs` (after `wstore`s into a fresh zero buffer). -/
macro "wbytes" : tactic => `(tactic| (
  (try simp only [List.replicate, List.take_succ_cons, List.take_zero, List.set_cons_succ,
    List.set_cons_zero])
  (try simp only [u32Le_sbytes_cons, u64Le_sbytes_cons, List.append_nil, List.append_assoc])))

set_option hygiene false in
/-- One `bs[i] = byte(...)` store into the slice `Hbs`. -/
macro "wstore" : tactic => `(tactic| (
  wp_apply wp_store_slice_index _ _ _ _ $$ [Hbs] as Hbs
  · iframe Hbs; ipureintro
    (try simp only [List.length_set, List.length_replicate, List.length_cons, List.length_nil,
      List.length_append, List.length_take, List.length_drop, u32Le_length, u64Le_length])
    first | decide | omega | simp
  (try wp_auto)))

/-- Lengths of byte lists built by the marshalers. -/
macro "blen" : tactic => `(tactic| (
  simp only [List.length_append, List.length_drop, List.length_cons, List.length_nil,
    List.length_replicate, List.length_take, u32Le_length, u64Le_length, List.length_set]
  first | rfl | decide | omega))

set_option hygiene false in
/-- One `bs[i]` load from the slice `Hbs` (a concrete list). -/
macro "wload" : tactic => `(tactic| (
  wp_apply wp_load_slice_index _ _ _ _ _ (by decide) $$ [Hbs] as Hbs
  · iframe Hbs; ipureintro; rfl
  (try wp_auto)))

theorem list8 {α} (d : List α) (h : d.length = 8) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7, d = [a0, a1, a2, a3, a4, a5, a6, a7] := by
  match d, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7], _ => exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩

theorem list4 {α} (d : List α) (h : d.length = 4) : ∃ a0 a1 a2 a3, d = [a0, a1, a2, a3] := by
  match d, h with
  | [a0, a1, a2, a3], _ => exact ⟨a0, a1, a2, a3, rfl⟩

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]

/-- `b[:n]` of a fresh local `[n]byte`. -/
theorem zero_array_slice' (b : Loc) (n : Nat) (hn : n < 2 ^ 63) :
    (b ↦ (zero_val (GoArray w8 (n : Int))) : IProp GF) ⊢
      slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) b) (W64 n - W64 0) (W64 n - W64 0) ↦*
        List.replicate n (W8 0) := by
  have hz : (zero_val (GoArray w8 (n : Int))).arr = List.replicate n (W8 0) := by
    simp [zero_val, ZeroVal.zeroValDef]
  iintro H
  ihave Hs := slice_array (GF := GF) b _ _ (by rw [hz]; simpa using hn) $$ H
  rw [hz, show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 (n : Int) - W64 0 = W64 n by
    simp]
  iexact Hs

theorem zero_array_slice (b : Loc) (n : Int) (m : Nat) (hm : n = m) (hn : m < 2 ^ 63) :
    (b ↦ (zero_val (GoArray w8 n)) : IProp GF) ⊢
      slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) b) (W64 n - W64 0) (W64 n - W64 0) ↦*
        List.replicate m (W8 0) := by
  subst hm; exact zero_array_slice' b m hn

/-- A fresh local `[n]byte` as an array value (`n` as the `w64` the code slices with). -/
theorem zero_array (b : Loc) (nn : w64) (n : Int) (h : sint.Z nn = n) (m : Nat) (hm : n = m) :
    (b ↦ (zero_val (GoArray w8 n)) : IProp GF) ⊢
      b ↦ (array.mk (sint.Z nn) (List.replicate m (W8 0)) : GoArray w8 (sint.Z nn)) := by
  subst h
  have hz : (zero_val (GoArray w8 (sint.Z nn))) = array.mk (sint.Z nn) (List.replicate m (W8 0)) := by
    simp [zero_val, ZeroVal.zeroValDef, hm]
  rw [hz]

/-- `b[:k]` of a local `[n]byte` array `b` (`0 < n`): the slice, and the way back. -/
theorem array_slice_acc (b : Loc) (L : List w8) (kk nn : w64) (k : Nat)
    (hk : sint.Z kk = k) (hn : sint.Z nn = L.length) (hkL : k ≤ L.length) (hpos : 0 < L.length) :
    (b ↦ (array.mk (sint.Z nn) L : GoArray w8 (sint.Z nn)) : IProp GF) ⊢
      slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) b) (kk - W64 0) (nn - W64 0) ↦* L.take k ∗
      (∀ L' : List w8, ⌜L'.length = k⌝ -∗
        slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) b) (kk - W64 0) (nn - W64 0) ↦* L' -∗
        b ↦ (array.mk (sint.Z nn) (L' ++ L.drop k) : GoArray w8 (sint.Z nn))) := by
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show kk - W64 0 = kk by simp,
    show nn - W64 0 = nn by simp]
  have hk0 : 0 ≤ sint.Z kk ∧ sint.Z kk ≤ sint.Z nn := by omega
  have hsk : sint.nat kk = k := by simp [sint.nat, hk]
  iintro H
  ihave ⟨H1, H2⟩ := (array_split kk b (DFrac.own 1) (sint.Z nn) (array.mk (sint.Z nn) L) hk0).1 $$ H
  rw [ownSlice_unseal]
  simp only [hsk]
  isplitl [H1]
  · unfold ownSliceDef; iright; iframe H1; ipureintro; simp; omega
  iintro %L' %hL' HL'
  unfold ownSliceDef
  icases HL' with (%Hnil | ⟨HL', -⟩)
  · exfalso; obtain ⟨h1, -⟩ := Hnil
    have h2 := congrArg GoSlice.cap h1
    simp [slice.nil] at h2
    subst h2
    have : sint.Z (0#64 : w64) = 0 := rfl
    omega
  iapply (array_split kk b (DFrac.own 1) (sint.Z nn) (array.mk (sint.Z nn) (L' ++ L.drop k)) hk0).2
  simp only [hsk, List.take_left' hL', List.drop_left' hL']
  iframe HL' H2

/-- A local `[n]byte` array whose contents no longer matter (only their length). -/
def arrBytes (b : Loc) (nn : w64) : IProp GF :=
  iprop(∃ L : List w8, ⌜(L.length : Int) = sint.Z nn⌝ ∗
    b ↦ (array.mk (sint.Z nn) L : GoArray w8 (sint.Z nn)))

theorem arrBytes_intro (b : Loc) (nn : w64) (L : List w8) (h : (L.length : Int) = sint.Z nn) :
    (b ↦ (array.mk (sint.Z nn) L : GoArray w8 (sint.Z nn)) : IProp GF) ⊢ arrBytes b nn := by
  iintro H; unfold arrBytes; iexists L; iframe H; ipureintro; exact h

/-- `b[:k]` of a local array whose contents no longer matter: some `k` bytes, and the way back. -/
theorem arrBytes_slice (b : Loc) (kk nn : w64) (k : Nat) (hk : sint.Z kk = k)
    (hkn : (k : Int) ≤ sint.Z nn) (hpos : 0 < sint.Z nn) :
    arrBytes (GF := GF) b nn ⊢ ∃ L : List w8, ⌜L.length = k⌝ ∗
      slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) b) (kk - W64 0) (nn - W64 0) ↦* L ∗
      (∀ L' : List w8, ⌜L'.length = k⌝ -∗
        slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) b) (kk - W64 0) (nn - W64 0) ↦* L' -∗
        arrBytes b nn) := by
  iintro H
  unfold arrBytes
  icases H with ⟨%L, %hL, H⟩
  ihave ⟨Hs, Hback⟩ := array_slice_acc b L kk nn k hk hL.symm (by omega) (by omega) $$ H
  iexists L.take k
  iframe Hs
  isplitr
  · ipureintro; simp; omega
  iintro %L' %hL' HL'
  ihave H := Hback $$ %L' %hL' HL'
  iexists L' ++ L.drop k
  iframe H
  ipureintro; simp; omega

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos
