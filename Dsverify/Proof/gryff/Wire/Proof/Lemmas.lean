/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Wire/Proof/Lemmas.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# U1 internal lemmas: the wire's generic steps

* Bytes: `u32Le_go`, `u64Le_go` (the bytes `byte(x >> 8j)` Go's generated `Marshal` stores are
  `u32Le` / `u64Le`), and their inverses for `Unmarshal`'s decoding.
* The byte buffer: `wp_store_byte` (a store into a `[]byte` slice over a local array, the bound
  a literal), the tactic `u1_wstore`.
* The writer: `wst bw wr J Q sent pend err D` (the bytes `D` have been offered to the
  `*bufio.Writer` since the state `sent pend err`, the frozen `Marshal` postcondition with `D`
  for the encoding); `wst_init`, `wst_done`; `wp_Write_sticky` (a `Write` on a writer with a
  sticky error writes nothing); `wp_wire_Write` (one `wire.Write(p)` step of `wst`).
-/
module

public import Dsverify.Proof.gryff.Wire.Enc
public import Proof.bufio.Writer__Write
public import Proof.bufio.Writer__Flush
public import Proof.bufio.ReaderLaws
public import Proof.bufio.Reader__ReadOk
public import Perennial.Proof.io.Link
public import Perennial.Proof.encoding.binary.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.wire

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Bytes -/

/-- An equation of bit vectors, bit by bit (kernel-checked; no `u1_bits_tac`). -/
macro "u1_bits_tac" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp (disch := omega) [BitVec.getElem_signExtend, BitVec.getElem_sshiftRight,
    BitVec.getLsbD_sshiftRight, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.sshiftRight', BitVec.ushiftRight_eq', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.shiftLeft_eq', BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
    BitVec.getLsbD_eq_getElem, decide_eq_false, decide_eq_true, BitVec.getLsbD_of_ge, if_pos, dif_pos,
    hi]
  try (intro h; omega)))

theorem u32Le_go (x : w32) : u32Le x = [W8 (sint.Z x), W8 (sint.Z (x.sshiftRight' (W64 8))),
    W8 (sint.Z (x.sshiftRight' (W64 16))), W8 (sint.Z (x.sshiftRight' (W64 24)))] := by
  simp only [u32Le, u32LeDef, LittleEndian.split, W8, sint.Z, Nat.div_div_eq_div_mul]
  have h1 : x.toNat / 256 = (x >>> 8).toNat := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : x.toNat / (256 * 256) = (x >>> 16).toNat := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h3 : x.toNat / (256 * 256 * 256) = (x >>> 24).toNat := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [h1, h2, h3]
  simp only [BitVec.ofNat_toNat, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (show _ = BitVec.signExtend 8 _; u1_bits_tac)

theorem u64Le_go (x : w64) : u64Le x = [W8 (uint.Z x), W8 (uint.Z (x >>> W64 8)),
    W8 (uint.Z (x >>> W64 16)), W8 (uint.Z (x >>> W64 24)), W8 (uint.Z (x >>> W64 32)),
    W8 (uint.Z (x >>> W64 40)), W8 (uint.Z (x >>> W64 48)), W8 (uint.Z (x >>> W64 56))] := by
  simp only [u64Le, u64LeDef, LittleEndian.split, W8, uint.Z, Nat.div_div_eq_div_mul]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul] <;> omega)

theorem w8_s64_0 (x : w64) : W8 (sint.Z x) = W8 (uint.Z x) := by
  simp only [W8, sint.Z, uint.Z]
  show BitVec.signExtend 8 x = BitVec.ofInt 8 (x.toNat : Int)
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  u1_bits_tac

theorem w8_s64_8 (x : w64) : W8 (uint.Z (x.sshiftRight' (W64 8))) = W8 (uint.Z (x >>> W64 8)) := by
  simp only [W8, uint.Z]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  u1_bits_tac

theorem w8_s64_16 (x : w64) : W8 (uint.Z (x.sshiftRight' (W64 16))) = W8 (uint.Z (x >>> W64 16)) := by
  simp only [W8, uint.Z]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  u1_bits_tac

theorem w8_s64_24 (x : w64) : W8 (uint.Z (x.sshiftRight' (W64 24))) = W8 (uint.Z (x >>> W64 24)) := by
  simp only [W8, uint.Z]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  u1_bits_tac

theorem w8_s64_32 (x : w64) : W8 (uint.Z (x.sshiftRight' (W64 32))) = W8 (uint.Z (x >>> W64 32)) := by
  simp only [W8, uint.Z]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  u1_bits_tac

theorem w8_s64_40 (x : w64) : W8 (uint.Z (x.sshiftRight' (W64 40))) = W8 (uint.Z (x >>> W64 40)) := by
  simp only [W8, uint.Z]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  u1_bits_tac

theorem w8_s64_48 (x : w64) : W8 (uint.Z (x.sshiftRight' (W64 48))) = W8 (uint.Z (x >>> W64 48)) := by
  simp only [W8, uint.Z]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  u1_bits_tac

theorem w8_s64_56 (x : w64) : W8 (uint.Z (x.sshiftRight' (W64 56))) = W8 (uint.Z (x >>> W64 56)) := by
  simp only [W8, uint.Z]
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  u1_bits_tac

theorem w32_of_w8 (a : w8) : W32 (uint.Z a) = a.setWidth 32 := by
  simp only [W32, uint.Z]
  apply BitVec.eq_of_toNat_eq
  simp

/-- `Unmarshal`'s decoding of an `int32`. -/
theorem u32Le_dec (a b c d : w8) :
    u32Le (W32 (uint.Z a) ||| W32 (uint.Z b) <<< W64 8 ||| W32 (uint.Z c) <<< W64 16 |||
      W32 (uint.Z d) <<< W64 24) = [a, b, c, d] := by
  rw [u32Le_go]
  simp only [w32_of_w8, List.cons.injEq, and_true, W8, sint.Z]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (show BitVec.signExtend 8 _ = _; u1_bits_tac)

theorem u64Le_dec (w0 w1 w2 w3 w4 w5 w6 w7 : w8) :
    u64Le (W64 (uint.Z w0) ||| (W64 (uint.Z w1) <<< W64 8) ||| (W64 (uint.Z w2) <<< W64 16) |||
      (W64 (uint.Z w3) <<< W64 24) ||| (W64 (uint.Z w4) <<< W64 32) |||
      (W64 (uint.Z w5) <<< W64 40) ||| (W64 (uint.Z w6) <<< W64 48) |||
      (W64 (uint.Z w7) <<< W64 56)) = [w0, w1, w2, w3, w4, w5, w6, w7] := by
  rw [← encoding.binary.leToU64_8, leToU64_le _ rfl]

theorem set5 {A : Type} (l : List A) (h : l.length = 5) (a b c d e : A) :
    ((((l.set 0 a).set 1 b).set 2 c).set 3 d).set 4 e = [a, b, c, d, e] := by
  match l, h with
  | [_, _, _, _, _], _ => rfl

theorem arrLe32_5 (a b c d e : w32) :
    arrLe32 (array.mk (5 : Int) [a, b, c, d, e]) = u32Le a ++ u32Le b ++ u32Le c ++ u32Le d ++ u32Le e := by
  simp [arrLe32, List.range_succ, List.flatMap_append]

/-- A load of a byte from a slice `b[:k]` of a local byte array `b`, held as the array. -/
theorem wp_load_byte_arr {GF : BundledGFunctors} [GooseExts] [GooseSemantics] [GooseInterp]
    [GoGlobalContext] [hG : HeapGS HasLC.hasLC GF] [go.Semantics]
    (p : Loc) (n : Int) (vs : List w8) (k c : w64) (i : Int) :
    {{ (typedPointsto p (array.mk n vs) (DFrac.own 1) ∗ ⌜0 ≤ i ∧ i < sint.Z k ∧ sint.Z k ≤ n⌝ :
        IProp GF) }}
      (App (Val (GoInstruction (GoLoad go.byte))) (Val #(sliceIndexRef w8 i (slice.mk p k c))))
    {{ RET #(vs.getD i.toNat (W8 0)); typedPointsto p (array.mk n vs) (DFrac.own 1) }} := by
  iintro %Φ ⟨Hp, %Hi⟩ HΦ
  ihave %Hl := array_len _ _ _ _ $$ Hp
  have hlt : i.toNat < vs.length := by omega
  have hv : vs[i.toNat]? = some (vs.getD i.toNat (W8 0)) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  icases array_acc (GF := GF) p i (DFrac.own 1) n (array.mk n vs) _ Hi.1 hv $$ Hp with ⟨Hv, Hback⟩
  simp only [sliceIndexRef]
  wp_apply IntoValTyped.wp_load (t := go.byte) _ _ _ $$ Hv as Hv
  iapply HΦ
  ihave Hp := Hback $$ Hv
  rw [list_set_lookup_self _ _ _ hv]
  iexact Hp

theorem flatMap_take_succ {A : Type} (l : List A) (f : A → List w8) (i : Nat) (c : A)
    (h : l[i]? = some c) : (l.take i).flatMap f ++ f c = (l.take (i + 1)).flatMap f := by
  rw [List.take_add_one, h]
  simp

theorem flatMap_take_prefix {A : Type} (l : List A) (f : A → List w8) (i : Nat) :
    (l.take i).flatMap f <+: l.flatMap f := by
  conv => rhs; rw [← List.take_append_drop i l]
  rw [List.flatMap_append]
  exact List.prefix_append _ _

/-- A list of known length is the list of its elements (`getD`). -/
theorem list_getD_eq (l : List w8) (n : Nat) (h : l.length = n) :
    l = (List.range n).map (fun i => l.getD i (W8 0)) := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

/-- The next element of a slice being filled in. -/
theorem list_fill_step {A : Type} (cs : List A) (z m : A) (len : Nat) (h : cs.length < len) :
    (cs ++ List.replicate (len - cs.length) z).set cs.length m =
      cs ++ [m] ++ List.replicate (len - (cs ++ [m]).length) z := by
  obtain ⟨k, hk⟩ : ∃ k, len - cs.length = k + 1 := ⟨len - cs.length - 1, by omega⟩
  rw [hk, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.replicate_succ,
    List.set_cons_zero]
  simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append]
  rw [show len - (cs.length + 1) = k by omega]

/-! ## The byte buffer -/

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A store of a byte into a slice over a local array (the bound a literal). -/
theorem wp_store_byte (p : Loc) (n c : w64) (i : Int) (vs : List w8) (v' : w8) :
    {{ (slice.mk p n c ↦* vs ∗ ⌜0 ≤ i ∧ i < sint.Z n⌝ : IProp GF) }}
      (App (Val (GoInstruction (GoStore go.byte)))
        (Val (PairV #(sliceIndexRef w8 i (slice.mk p n c)) #v')))
    {{ RET #(); slice.mk p n c ↦* vs.set i.toNat v' }} := by
  iintro %Φ ⟨Hs, %Hb⟩ HΦ
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  wp_apply wp_store_slice_index (V := w8) _ i vs v' $$ [$Hs] as Hs
  · ipureintro
    have : (vs.length : Int) = sint.Z n := by rw [Hl.1]; exact Int.toNat_of_nonneg Hl.2
    omega
  iapply HΦ $$ Hs

/-- Name the value of a points-to (a Lean variable for a value the code computed). -/
theorem pt_name {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (l : Loc) (v : V)
    (dq : DFrac) :
    typedPointsto (GF := GF) l v dq ⊢ ∃ x : V, typedPointsto l x dq ∗ ⌜x = v⌝ := by
  iintro H
  iexists v
  iframe H
  ipureintro; rfl

/-- A local byte array's contents as the list of its elements (`getD`), for stores that
overwrite it. -/
theorem array_explicit (p : Loc) (n : Int) (vs : List w8) (dq : DFrac) :
    typedPointsto (GF := GF) p (array.mk n vs) dq ⊢
      typedPointsto p (array.mk n ((List.range n.toNat).map (fun i => vs.getD i (W8 0)))) dq := by
  iintro H
  ihave %Hl := array_len _ _ _ _ $$ H
  rw [← list_getD_eq vs n.toNat (by omega)]
  iexact H

/-- A store into an element of an `[n]int32` array (the index a literal). -/
theorem wp_store_arr32 (p : Loc) (n : Int) (a : GoArray w32 n) (i : Int) (v' : w32) :
    {{ (typedPointsto p a (DFrac.own 1) ∗ ⌜0 ≤ i ∧ i < n⌝ : IProp GF) }}
      (App (Val (GoInstruction (GoStore go.int32))) (Val (PairV #(arrayIndexRef w32 i p) #v')))
    {{ RET #(); typedPointsto p (array.mk n (a.arr.set i.toNat v')) (DFrac.own 1) }} := by
  obtain ⟨vs⟩ := a
  iintro %Φ ⟨Hp, %Hi⟩ HΦ
  ihave %Hl := array_len _ _ _ _ $$ Hp
  obtain ⟨v, hv⟩ : ∃ v, vs[i.toNat]? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases array_acc (GF := GF) p i (DFrac.own 1) n (array.mk n vs) v Hi.1 hv $$ Hp with ⟨Hv, Hback⟩
  wp_apply IntoValTyped.wp_store (t := go.int32) _ _ _ $$ Hv as Hv
  iapply HΦ
  iapply Hback $$ Hv

/-- A load of an element of an `[n]int32` array (the index a literal). -/
theorem wp_load_arr32 (p : Loc) (n : Int) (a : GoArray w32 n) (i : Int) (dq : DFrac) :
    {{ (typedPointsto p a dq ∗ ⌜0 ≤ i ∧ i < n⌝ : IProp GF) }}
      (App (Val (GoInstruction (GoLoad go.int32))) (Val #(arrayIndexRef w32 i p)))
    {{ RET #(a.arr.getD i.toNat (W32 0)); typedPointsto p a dq }} := by
  obtain ⟨vs⟩ := a
  iintro %Φ ⟨Hp, %Hi⟩ HΦ
  ihave %Hl := array_len _ _ _ _ $$ Hp
  have hlt : i.toNat < vs.length := by omega
  have hv : vs[i.toNat]? = some (vs.getD i.toNat (W32 0)) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  icases array_acc (GF := GF) p i dq n (array.mk n vs) _ Hi.1 hv $$ Hp with ⟨Hv, Hback⟩
  wp_apply IntoValTyped.wp_load (t := go.int32) _ _ _ $$ Hv as Hv
  iapply HΦ
  ihave Hp := Hback $$ Hv
  rw [list_set_lookup_self _ _ _ hv]
  iexact Hp

/-- A store of a byte into a slice `b[:k]` of a local byte array `b`, held as the array. -/
theorem wp_store_byte_arr (p : Loc) (n : Int) (vs : List w8) (k c : w64) (i : Int) (v' : w8) :
    {{ (typedPointsto p (array.mk n vs) (DFrac.own 1) ∗ ⌜0 ≤ i ∧ i < sint.Z k ∧ sint.Z k ≤ n⌝ :
        IProp GF) }}
      (App (Val (GoInstruction (GoStore go.byte)))
        (Val (PairV #(sliceIndexRef w8 i (slice.mk p k c)) #v')))
    {{ RET #(); typedPointsto p (array.mk n (vs.set i.toNat v')) (DFrac.own 1) }} := by
  iintro %Φ ⟨Hp, %Hi⟩ HΦ
  ihave %Hl := array_len _ _ _ _ $$ Hp
  obtain ⟨v, hv⟩ : ∃ v, vs[i.toNat]? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases array_acc (GF := GF) p i (DFrac.own 1) n (array.mk n vs) v Hi.1 hv $$ Hp with ⟨Hv, Hback⟩
  simp only [sliceIndexRef]
  wp_apply IntoValTyped.wp_store (t := go.byte) _ _ _ $$ Hv as Hv
  iapply HΦ
  iapply Hback $$ Hv

/-- A prefix `b[:k]` of a local array as a slice, and the rest of the array. -/
theorem array_prefix_slice (p : Loc) (k c : w64) (n : Int) (vs : List w8)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ n) (hc : sint.Z k ≤ sint.Z c) :
    typedPointsto (GF := GF) p (array.mk n vs) (DFrac.own 1) ⊢
      slice.mk p k c ↦* vs.take (sint.nat k) ∗
      typedPointsto (arrayIndexRef w8 (sint.Z k) p)
        (array.mk (n - sint.Z k) (vs.drop (sint.nat k))) (DFrac.own 1) := by
  iintro H
  icases (array_split (GF := GF) k p (DFrac.own 1) n (array.mk n vs) hk).1 $$ H with ⟨H1, H2⟩
  iframe H2
  rw [ownSlice_unseal]; unfold ownSliceDef
  iright
  iframe H1
  ipureintro; exact hc

/-- The prefix slice `b[:k]` and the rest of the array put back together. -/
theorem array_of_prefix_slice (p : Loc) (k c : w64) (m : Int) (vs rest : List w8) :
    (slice.mk p k c ↦* vs ∗
      typedPointsto (arrayIndexRef w8 (sint.Z k) p) (array.mk m rest) (DFrac.own 1) : IProp GF) ⊢
      typedPointsto p (array.mk (sint.Z k + m) (vs ++ rest)) (DFrac.own 1) := by
  iintro ⟨H1, H2⟩
  ihave %Hl := ownSlice_len _ _ _ $$ H1
  ihave %Hl2 := array_len _ _ _ _ $$ H2
  obtain ⟨hl1, hl2⟩ := Hl
  have hk : sint.nat k = vs.length := hl1.symm
  have ht : (vs ++ rest).take (sint.nat k) = vs := by rw [hk]; simp
  have hd : (vs ++ rest).drop (sint.nat k) = rest := by rw [hk]; simp
  have hm : 0 ≤ m := by rw [Hl2]; omega
  have e := array_split (GF := GF) k p (DFrac.own 1) (sint.Z k + m) (array.mk _ (vs ++ rest))
    ⟨hl2, by omega⟩
  simp only [ht, hd] at e
  rw [ownSlice_unseal]; unfold ownSliceDef
  icases H1 with (%H | ⟨H1, %_⟩)
  · obtain ⟨h1, rfl⟩ := H
    simp only [slice.nil, slice.mk, GoSlice.mk.injEq] at h1
    obtain ⟨rfl, rfl, -⟩ := h1
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ H2
    exfalso; apply Hnn
    rw [show sint.Z (0 : w64) = 0 from rfl, go.arrayIndexRef_0]
  iapply e.2
  rw [show sint.Z k + m - sint.Z k = m by omega]
  iframe H2
  iexact H1

end heap

theorem zero_arr_w8 (n : Int) : (zero_val (GoArray w8 n)).arr = List.replicate n.toNat (zero_val w8) :=
  rfl

theorem sint_Z_W64_0 : sint.Z (W64 0) = 0 := rfl

theorem w64_sub_zero (x : w64) : x - W64 0 = x := by
  simp [W64]

theorem zero_val_arr_w8 (n : Int) :
    zero_val (GoArray w8 n) = array.mk n (List.replicate n.toNat (zero_val w8)) := rfl

/-- The buffer's list of stores normalized to a list literal. -/
macro "u1_buf_norm" : tactic => `(tactic| ((try word_lit_simp); simp only [zero_arr_w8, zero_val_arr_w8,
  Int.toNat_zero, Int.reduceToNat, List.replicate_succ, List.replicate_zero, List.set_cons_zero,
  List.set_cons_succ, List.take_succ_cons, List.take_zero, List.take_nil]))

set_option hygiene false in
/-- One load of a byte from the buffer `Hb`. -/
macro "u1_wload" : tactic =>
  `(tactic| (wp_apply wp_load_byte $$ [Hb] as Hb; (iframe; ipureintro; try word); try wp_auto))

set_option hygiene false in
/-- One store into an element of the `[5]int32` field `Deps`. -/
macro "u1_wstore_deps" : tactic => `(tactic| first
  | (wp_apply wp_store_arr32 $$ [Deps] as Deps; (iframe; ipureintro; try word); try wp_auto)
  | (wp_apply wp_store_arr32 $$ [CommittedDeps] as CommittedDeps
     (iframe; ipureintro; try word)
     try wp_auto))

set_option hygiene false in
/-- One store of a byte into the local array `b`. -/
macro "u1_wstore_b" : tactic =>
  `(tactic| (
    (try simp only [sint_Z_W64_0, go.arrayIndexRef_0, w64_sub_zero, zero_val_arr_w8])
    wp_apply wp_store_byte_arr $$ [b] as b
    (iframe; ipureintro; try word)
    try wp_auto))

set_option hygiene false in
/-- One store of a byte into the buffer `Hb`. -/
macro "u1_wstore" : tactic =>
  `(tactic| (wp_apply wp_store_byte $$ [Hb] as Hb; (iframe; ipureintro; try word); try wp_auto))

/-! ## The writer

The lab's harness `bufio` (`ownWriter bw wr J Q sent pend err`, `writerOk wr J Q`) is replaced by
dsv-bufio's (`EtcdGrove.bufio.ownBufWriter`, `EtcdGrove.io.streamWriterOk`), never unfolded here.
Its extra fixed parameters (the wrapped writer as a `GoInterfaceOk`, its errors' evidence `Ew`,
the buffer's size `sz`) are bundled as `WSt`, so that the lab's `wr J Q` shapes stay. -/

/-- A `*bufio.Writer`'s fixed parameters (see the section header). -/
structure WSt [GooseExts] (GF : BundledGFunctors) where
  wi : GoInterfaceOk
  Ew : GoInterface → IProp GF
  sz : Nat

section writer
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The wrapped writer's contract (the lab's `bufio.writerOk`). -/
abbrev writerOk (wr : WSt GF) (J Q : List w8 → IProp GF) : IProp GF :=
  EtcdGrove.io.streamWriterOk wr.wi J Q wr.Ew

/-- The `*bufio.Writer` `bw` has sent `sent` and buffers `pend`, with the sticky error `err` (the
lab's `bufio.ownWriter`). -/
abbrev ownWriter (bw : Loc) (wr : WSt GF) (J Q : List w8 → IProp GF) (sent pend : List w8)
    (err : GoInterface) : IProp GF :=
  EtcdGrove.bufio.ownBufWriter bw wr.wi J Q wr.Ew wr.sz sent pend err

/-- The bytes `D` have been offered to the writer `bw` since the state `sent pend err`: the
frozen `Marshal` postcondition, without the message. -/
def wst (bw : Loc) (wr : WSt GF) (J Q : List w8 → IProp GF) (sent pend : List w8)
    (err : GoInterface) (D : List w8) : IProp GF :=
  iprop(∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
    ⌜k ≤ D.length ∧ sent' ++ pend' = sent ++ pend ++ D.take k ∧ sent <+: sent' ∧
      (err' = interface.nil → k = D.length) ∧ (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
    ownWriter bw wr J Q sent' pend' err')

theorem wst_init (bw : Loc) (wr : WSt GF) (J Q : List w8 → IProp GF) (sent pend : List w8)
    (err : GoInterface) :
    ownWriter bw wr J Q sent pend err ⊢ wst bw wr J Q sent pend err [] := by
  iintro H
  unfold wst
  iexists 0, sent, pend, err
  iframe H
  ipureintro
  simp

theorem wst_done (bw : Loc) (wr : WSt GF) (J Q : List w8 → IProp GF) (sent pend : List w8)
    (err : GoInterface) (D : List w8) :
    wst bw wr J Q sent pend err D ⊢ ∃ (k : Nat) (sent' pend' : List w8) (err' : GoInterface),
      ⌜k ≤ D.length ∧ sent' ++ pend' = sent ++ pend ++ D.take k ∧ sent <+: sent' ∧
        (err' = interface.nil → k = D.length) ∧ (err ≠ interface.nil → err' = err ∧ k = 0)⌝ ∗
      ownWriter bw wr J Q sent' pend' err' := by
  unfold wst; exact .rfl

variable [bufio.Assumptions]

set_option goose.wp.extras true

/-- One `wire.Write(p)` of `Marshal`: the bytes `ps` are offered after `D`, where `D ++ ps` is a
prefix of the allowed stream's continuation `E0` (dsv-bufio's `Writer.Write.spec`; a writer with
a sticky error writes nothing). -/
theorem wp_wire_Write (bw : Loc) (wr : WSt GF) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) (E0 D : List w8) (p : GoSlice) (dq : DFrac)
    (ps : List w8) :
    {{ writerOk wr J Q ∗ □ Q (sent ++ pend ++ E0) ∗
        ⌜D ++ ps <+: E0⌝ ∗ wst bw wr J Q sent pend err D ∗ p ↦*{dq} ps }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"Write")) (Val #p))
    {{ (nn : w64) (e : GoInterface), RET (PairV #nn #e);
        wst bw wr J Q sent pend err (D ++ ps) ∗ p ↦*{dq} ps }} := by
  wp_start_folded as ⟨#Hwr, #HQ, %Hpre, Hw, Hp⟩
  unfold wst
  icases Hw with ⟨%k, %sent', %pend', %err', %Hk, Hown⟩
  obtain ⟨hk, hs, hpre, hnil, herr⟩ := Hk
  ihave #Hpc := EtcdGrove.io.streamWriterOk_prefixClosed _ _ _ _ $$ Hwr
  ihave HQ' : (⌜err' = interface.nil⌝ -∗ □ Q (sent' ++ pend' ++ ps)) $$ []
  · iintro %he
    have hkD : k = D.length := hnil he
    subst hkD
    rw [List.take_length] at hs
    iunfold EtcdGrove.io.prefixClosed at Hpc
    iapply EtcdGrove.bufio.Q_of_prefix Q (sent' ++ pend' ++ ps) (sent ++ pend ++ E0)
      (by rw [hs, List.append_assoc (sent ++ pend)]
          exact (List.prefix_append_right_inj _).mpr Hpre) $$ Hpc HQ
  wp_apply EtcdGrove.bufio.Writer.Write.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof bw wr.wi J Q wr.Ew wr.sz sent' pend' err' p dq ps
    $$ [$Hown $HQ' $Hp] as %nn %e2 ⟨%k2, %sent'', %pend'', %Hk2, Hp, Hown⟩
  obtain ⟨-, hk2, hs2, hpre2, hnil2, herr2, -⟩ := Hk2
  iapply HΦ
  iframe Hp
  by_cases he : err' = interface.nil
  · subst he
    have hkD : k = D.length := hnil rfl
    subst hkD
    rw [List.take_length] at hs
    iexists D.length + k2, sent'', pend'', e2
    iframe Hown
    ipureintro
    refine ⟨by simp; omega, ?_, hpre.trans hpre2, fun h => by simp [hnil2 h], fun h => ?_⟩
    · rw [hs2, hs, List.take_append]
      simp [List.append_assoc, List.take_of_length_le (show D.length ≤ D.length + k2 by omega)]
    · exact absurd (herr h).1.symm (by simpa using h)
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := herr2 he
    iexists k, sent'', pend'', e2
    iframe Hown
    ipureintro
    refine ⟨by simp; omega, ?_, hpre, fun h => absurd h he, herr⟩
    rw [hs, List.take_append_of_le_length hk]

/-- `wire.Write(b[:k])` of a local byte array `b` (held as the array). -/
theorem wp_wire_Write_arr (bw : Loc) (wr : WSt GF) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) (E0 D : List w8) (p : Loc) (n : Int)
    (vs : List w8) (k c : w64) :
    {{ writerOk wr J Q ∗ □ Q (sent ++ pend ++ E0) ∗
        ⌜D ++ vs.take (sint.nat k) <+: E0 ∧ 0 ≤ sint.Z k ∧ sint.Z k ≤ n ∧ sint.Z k ≤ sint.Z c⌝ ∗
        wst bw wr J Q sent pend err D ∗ typedPointsto p (array.mk n vs) (DFrac.own 1) }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"Write"))
        (Val #(slice.mk p k c)))
    {{ (nn : w64) (e : GoInterface), RET (PairV #nn #e);
        wst bw wr J Q sent pend err (D ++ vs.take (sint.nat k)) ∗
        typedPointsto p (array.mk n vs) (DFrac.own 1) }} := by
  wp_start_folded as ⟨#Hwr, #HQ, %Hpre, Hw, Hp⟩
  obtain ⟨hpre, hk0, hkn, hkc⟩ := Hpre
  ihave %Hl := array_len _ _ _ _ $$ Hp
  ihave ⟨Hs, Hrest⟩ := array_prefix_slice (GF := GF) p k c n vs ⟨hk0, hkn⟩ hkc $$ Hp
  wp_apply wp_wire_Write bw wr J Q sent pend err E0 D _ (DFrac.own 1) _ $$ [$Hwr $HQ $Hw $Hs]
    as %nn %e ⟨Hw, Hs⟩
  · ipureintro; exact hpre
  iapply HΦ
  iframe Hw
  ihave Hp := array_of_prefix_slice (GF := GF) p k c _ _ _ $$ [$Hs $Hrest]
  rw [List.take_append_drop, show sint.Z k + (n - sint.Z k) = n by omega]
  iexact Hp

theorem wst_name (bw : Loc) (wr : WSt GF) (J Q : List w8 → IProp GF) (sent pend : List w8)
    (err : GoInterface) (D1 : List w8) :
    wst bw wr J Q sent pend err D1 ⊢ ∃ D2, wst bw wr J Q sent pend err D2 ∗ ⌜D2 = D1⌝ := by
  iintro H; iexists D1; iframe H; ipureintro; rfl

theorem wst_congr (bw : Loc) (wr : WSt GF) (J Q : List w8 → IProp GF) (sent pend : List w8)
    (err : GoInterface) (D1 D2 : List w8) (h : D1 = D2) :
    wst bw wr J Q sent pend err D1 ⊢ wst bw wr J Q sent pend err D2 := by
  rw [h]

end writer

/-! ## The reader

The lab's harness `bufio` (`ownReader br rd I R`, `readerOk rd I`) is replaced by dsv-bufio's
`EtcdGrove.bufio.ownBufReader` (never unfolded here), its reads' condition fixed to
`fun _ m => 0 < m` (what a connection's reader, `net.conn_readerOk`, gives). Its fixed parameters
(the wrapped reader, its errors' evidence `E`) are bundled as `RSt`; `I` is the stream state.
`Perennial`'s `io.ReadAtLeast`/`io.ReadFull` read through it (`bufio.ownBufReader_readerOk`). An
error a message's `Unmarshal` returns is `rdErr`: a read error of the reader, or one of the
`io`/`encoding/binary` errors (`ErrUnexpectedEOF`, `ErrShortBuffer`, `errOverflow`), in place of
the lab's `net.rpc.errAny err ∗ ⌜errWf err⌝` (the user of a connection proves those from its
`E`). -/

/-- A `*bufio.Reader`'s fixed parameters (see the section header). -/
structure RSt [GooseExts] (GF : BundledGFunctors) where
  ri : GoInterfaceOk
  E : List w8 → GoInterface → IProp GF

section reader
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The `*bufio.Reader` `br` has returned `R` (the lab's `bufio.ownReader`). -/
abbrev ownReader (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (R : List w8) : IProp GF :=
  EtcdGrove.bufio.ownBufReader br rd.ri (fun _ m => 0 < m) I rd.E R

/-- What a read needs besides the reader (the lab's `bufio.readerOk`): `io` and `bufio`
initialized. -/
def readerOk (_rd : RSt GF) (_I : List w8 → IProp GF) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.io ∗ isPkgInit (PROP := IProp GF) pkg_id.bufio)

instance readerOk_persistent (rd : RSt GF) (I : List w8 → IProp GF) :
    Persistent (readerOk rd I) := by
  unfold readerOk; infer_instance

/-- An error a read of a message returned (see the section header). -/
def rdErr (rd : RSt GF) (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ interface.nil⌝ ∗
    □ ((∃ r, EtcdGrove.bufio.errE rd.E r err) ∨
      globalAddr io.ErrUnexpectedEOF ↦□ err ∨ globalAddr io.ErrShortBuffer ↦□ err ∨
      globalAddr encoding.binary.errOverflow ↦□ err))

instance rdErr_persistent (rd : RSt GF) (err : GoInterface) : Persistent (rdErr rd err) := by
  unfold rdErr; infer_instance

theorem rdErr_ne (rd : RSt GF) (err : GoInterface) : rdErr rd err ⊢ ⌜err ≠ interface.nil⌝ := by
  unfold rdErr; iintro ⟨%H, -⟩; ipureintro; exact H

/-- A load of a byte from a slice over a local array (the bound a literal). -/
theorem wp_load_byte (p : Loc) (n c : w64) (i : Int) (vs : List w8) (dq : DFrac) :
    {{ (slice.mk p n c ↦*{dq} vs ∗ ⌜0 ≤ i ∧ i < sint.Z n⌝ : IProp GF) }}
      (App (Val (GoInstruction (GoLoad go.byte))) (Val #(sliceIndexRef w8 i (slice.mk p n c))))
    {{ RET #(vs.getD i.toNat (W8 0)); slice.mk p n c ↦*{dq} vs }} := by
  iintro %Φ ⟨Hs, %Hb⟩ HΦ
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have hl : (vs.length : Int) = sint.Z n := by rw [Hl.1]; exact Int.toNat_of_nonneg Hl.2
  have hlt : i.toNat < vs.length := by omega
  wp_apply wp_load_slice_index (V := w8) _ i vs dq (vs.getD i.toNat (W8 0)) Hb.1 $$ [$Hs] as Hs
  · ipureintro
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  iapply HΦ $$ Hs

variable [bufio.Assumptions] [io.Assumptions]

/-- `io.ReadAtLeast(wire, bs, len(bs))` on the `*bufio.Reader` `br` (as an `io.Reader`): all of
`bs` read (`err = nil`), or an error (`rdErr`) with some bytes read. -/
theorem wp_wire_ReadAtLeast (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF)
    (R : List w8) (sl : GoSlice) (vs : List w8) :
    {{ readerOk rd I ∗ ownReader br rd I R ∗ sl ↦* vs }}
      (App (App (App (Val (@! io.ReadAtLeast))
          (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br))) (Val #sl))
        (Val #sl.len))
    {{ (nr : w64) (err : GoInterface), RET (PairV #nr #err); ∃ data : List w8,
        ownReader br rd I (R ++ data) ∗
        ((⌜err = interface.nil ∧ data.length = vs.length⌝ ∗ sl ↦* data) ∨
         (rdErr rd err ∗ ∃ vs' : List w8, sl ↦* vs')) }} := by
  wp_start_folded as ⟨#Hrd, Hown, Hs⟩
  iunfold readerOk at Hrd
  icases Hrd with ⟨#Hio, #Hbuf⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have hl : (vs.length : Int) = sint.Z sl.len := by rw [Hl.1]; exact Int.toNat_of_nonneg Hl.2
  ihave #Hinit := io.isInit_access $$ Hio
  icases Hinit with ⟨-, -, -, #HSB, #HEOF, #HUE, -⟩
  iunfold errors.newVar at HSB HEOF HUE
  icases HSB with ⟨%sbl, #Hsb, -⟩
  icases HEOF with ⟨%eofl, #Heof, -⟩
  icases HUE with ⟨%ueofl, #Hueof, -⟩
  ihave #HrOk := EtcdGrove.bufio.ownBufReader_readerOk EtcdGrove.bufio.Reader.Read.wp_proofOk br
    rd.ri (fun _ m => 0 < m) I rd.E
  rw [show interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br =
    GoInterface.ok (EtcdGrove.bufio.readerIface br) from rfl]
  wp_apply io.wp_ReadAtLeast (EtcdGrove.bufio.readerIface br) _ _ _ R sl vs sl.len _ _ _
    $$ [$Hio $HrOk $Heof $Hueof $Hsb $Hown $Hs] as %nr %err ⟨%data, %Hd, Hs, Hown, #Hres⟩
  · ipureintro; intro _ _ h; exact h
  obtain ⟨-, hdl⟩ := Hd
  iapply HΦ
  iexists data
  iframe Hown
  iunfold io.readAtLeastRes at Hres
  icases Hres with (%Hsb' | (%Hok | ⟨%e, %He, #HE⟩))
  · obtain ⟨h, -, -⟩ := Hsb'; exfalso; omega
  · obtain ⟨-, h2, rfl⟩ := Hok
    ileft
    have : data.length = vs.length := by omega
    rw [this, List.drop_length, List.append_nil]
    iframe Hs
    ipureintro; exact ⟨rfl, rfl⟩
  · obtain ⟨-, hlt, hne, hueof, hother⟩ := He
    iright
    isplitr
    · unfold rdErr
      by_cases hx : e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #eofl ∧
          data ≠ []
      · rw [hueof hx]
        isplitr
        · ipureintro; intro h; cases h
        imodintro; iright; ileft; iexact Hueof
      · rw [hother hx]
        isplitr
        · ipureintro; exact hne
        imodintro; ileft; iexists _; iexact HE
    iexists _; iexact Hs

/-- `io.ReadAtLeast(wire, b[:k], k)` into a local byte array `b` (held as the array). -/
theorem wp_wire_ReadAtLeast_arr (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF)
    (R : List w8) (p : Loc) (n : Int) (vs : List w8) (k c : w64) :
    {{ readerOk rd I ∗ ownReader br rd I R ∗ typedPointsto p (array.mk n vs) (DFrac.own 1) ∗
        ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ n ∧ sint.Z k ≤ sint.Z c⌝ }}
      (App (App (App (Val (@! io.ReadAtLeast))
          (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
          (Val #(slice.mk p k c))) (Val #k))
    {{ (nr : w64) (err : GoInterface), RET (PairV #nr #err); ∃ data : List w8,
        ownReader br rd I (R ++ data) ∗
        ((⌜err = interface.nil ∧ data.length = sint.nat k⌝ ∗
            typedPointsto p (array.mk n (data ++ vs.drop (sint.nat k))) (DFrac.own 1)) ∨
         (rdErr rd err ∗ ∃ vs' : List w8,
            typedPointsto p (array.mk n vs') (DFrac.own 1))) }} := by
  wp_start_folded as ⟨#Hrd, Hown, Hp, %Hk⟩
  obtain ⟨hk0, hkn, hkc⟩ := Hk
  ihave %Hvl := array_len _ _ _ _ $$ Hp
  ihave ⟨Hs, Hrest⟩ := array_prefix_slice (GF := GF) p k c n vs ⟨hk0, hkn⟩ hkc $$ Hp
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  have hsk : (slice.mk p k c).len = k := rfl
  rw [hsk] at Hsl
  wp_apply wp_wire_ReadAtLeast br rd I R (slice.mk p k c) _ $$ [$Hrd $Hown $Hs]
    as %nr %err ⟨%data, Hown, Hr⟩
  iapply HΦ
  iexists data
  iframe Hown
  icases Hr with (⟨⟨%Hnil, %Hlen⟩, Hs⟩ | ⟨#Ha, %vs', Hs⟩)
  · ileft
    ihave Hp := array_of_prefix_slice (GF := GF) p k c _ _ _ $$ [$Hs $Hrest]
    rw [show sint.Z k + (n - sint.Z k) = n by omega]
    iframe Hp
    ipureintro
    refine ⟨Hnil, ?_⟩
    have h1 : ((sint.nat k : Nat) : Int) = sint.Z k := Int.toNat_of_nonneg hk0
    rw [Hlen, List.length_take]
    omega
  · iright
    iframe Ha
    ihave Hp := array_of_prefix_slice (GF := GF) p k c _ _ _ $$ [$Hs $Hrest]
    rw [show sint.Z k + (n - sint.Z k) = n by omega]
    iexists _
    iexact Hp

theorem ownReader_eq (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (X Y : List w8)
    (h : X = Y) : ownReader br rd I X ⊢ ownReader br rd I Y := by
  rw [h]

theorem ownReader_app_eq (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (R D1 D2 : List w8)
    (h : D1 = D2) : ownReader br rd I (R ++ D1) ⊢ ownReader br rd I (R ++ D2) := by
  rw [h]

end reader

/-- The encodings unfolded to bytes. -/
macro "u1_enc_norm" : tactic => `(tactic| (try word_lit_simp) <;> simp only [
  state.Key.enc, state.Value.enc, state.Command.enc, gryffproto.Tag.enc,
  gryffproto.ValTag.enc, gryffproto.Dep.enc, gryffproto.Read.enc, gryffproto.ReadReply.enc,
  gryffproto.Write.enc, gryffproto.WriteReply.enc, gryffproto.RMW.enc, gryffproto.RMWReply.enc,
  gryffproto.Read1Proxied.enc, gryffproto.Read1Reply.enc, gryffproto.Read2Proxied.enc, gryffproto.Read2Reply.enc,
  gryffproto.Write1Proxied.enc, gryffproto.Write1Reply.enc, gryffproto.Write2Proxied.enc, gryffproto.Write2Reply.enc,
  gryffproto.PreAccept.enc, gryffproto.PreAcceptReply.enc, gryffproto.EAccept.enc, gryffproto.ECommit.enc,
  gryffproto.TryPreAccept.enc, gryffproto.PrepareReply.enc, gryffproto.Executed.enc, gryffproto.PreAcceptOKReply.enc,
  gryffproto.AcceptOKReply.enc, epaxosproto.Prepare.enc, epaxosproto.PreAcceptOK.enc, epaxosproto.AcceptReply.enc,
  epaxosproto.CommitShort.enc, epaxosproto.TryPreAcceptReply.enc, clientproto.Ping.enc, clientproto.PingReply.enc,
  genericsmrproto.Beacon.enc, genericsmrproto.BeaconReply.enc, genericsmrproto.Propose.enc, genericsmrproto.ProposeReplyTS.enc,
  u32Le_go, u64Le_go, List.take_succ_cons, List.take_zero, List.take_nil,
  w8_s64_0, w8_s64_8, w8_s64_16, w8_s64_24, w8_s64_32, w8_s64_40, w8_s64_48, w8_s64_56,
  arrLe32, List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_cons,
  List.flatMap_nil, Int.reduceToNat, List.getD_cons_zero, List.getD_cons_succ,
  List.cons_append, List.nil_append, List.append_assoc, List.singleton_append, List.append_nil])

/-- The bytes read, `data` (of length `h : data.length = n`), are the encoding of the decoded
message. -/
macro "u1_dec_tac" h:term : tactic => `(tactic| (
  conv => lhs; rw [list_getD_eq _ _ $h]
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.singleton_append]
  simp only [
  state.Key.enc, state.Value.enc, state.Command.enc, gryffproto.Tag.enc,
  gryffproto.ValTag.enc, gryffproto.Dep.enc, gryffproto.Read.enc, gryffproto.ReadReply.enc,
  gryffproto.Write.enc, gryffproto.WriteReply.enc, gryffproto.RMW.enc, gryffproto.RMWReply.enc,
  gryffproto.Read1Proxied.enc, gryffproto.Read1Reply.enc, gryffproto.Read2Proxied.enc, gryffproto.Read2Reply.enc,
  gryffproto.Write1Proxied.enc, gryffproto.Write1Reply.enc, gryffproto.Write2Proxied.enc, gryffproto.Write2Reply.enc,
  gryffproto.PreAccept.enc, gryffproto.PreAcceptReply.enc, gryffproto.EAccept.enc, gryffproto.ECommit.enc,
  gryffproto.TryPreAccept.enc, gryffproto.PrepareReply.enc, gryffproto.Executed.enc, gryffproto.PreAcceptOKReply.enc,
  gryffproto.AcceptOKReply.enc, epaxosproto.Prepare.enc, epaxosproto.PreAcceptOK.enc, epaxosproto.AcceptReply.enc,
  epaxosproto.CommitShort.enc, epaxosproto.TryPreAcceptReply.enc, clientproto.Ping.enc, clientproto.PingReply.enc,
  genericsmrproto.Beacon.enc, genericsmrproto.BeaconReply.enc, genericsmrproto.Propose.enc, genericsmrproto.ProposeReplyTS.enc,
  u32Le_dec, u64Le_dec,
  List.cons_append, List.nil_append, List.append_assoc, List.singleton_append, List.append_nil]))

set_option hygiene false in
/-- A prefix goal `D ++ ps <+: E0` of a `Marshal` step, from `Hpre : D0 ++ enc m <+: E0`. -/
macro "u1_prefix_tac" : tactic => `(tactic| (
  refine List.IsPrefix.trans ?_ Hpre
  try simp only [List.append_assoc]
  apply (List.prefix_append_right_inj _).mpr
  u1_enc_norm
  first
  | exact List.prefix_refl _
  | exact List.prefix_append _ _
  | (repeat (first | apply (List.prefix_cons_inj _).mpr | apply (List.prefix_append_right_inj _).mpr)
     first | exact List.nil_prefix | exact List.prefix_refl _ | exact List.prefix_append _ _)))

set_option hygiene false in
/-- `wire.Write(bs)` of the buffer `Hb`, the prefix condition from `Hpre`. -/
macro "u1_marshal_write" : tactic => `(tactic| (
  wp_apply (wp_wire_Write (E0 := E0)) $$ [Hw Hb] as %nn %e ⟨Hw, Hb⟩
  · iframe Hwr HQ Hw Hb; ipureintro; u1_prefix_tac))

set_option hygiene false in
/-- The end of a `Marshal`: the bytes written are the encoding; the struct's fields put back
together (`Hnn`). -/
macro "u1_marshal_finish" : tactic => `(tactic| (
  iapply HΦ
  isplitl [Hw]
  · iapply wst_congr _ _ _ _ _ _ _ _ _ (by u1_enc_norm <;> rfl) $$ Hw
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe))

set_option hygiene false in
/-- `wire.Write(b[:k])` of the local array `b`, the prefix condition from `Hpre`. -/
macro "u1_write_b" : tactic => `(tactic| (
  (try u1_buf_norm)
  wp_apply (wp_wire_Write_arr (E0 := E0)) $$ [Hw b] as %nn %e ⟨Hw, b⟩
  · iframe Hwr HQ Hw b; ipureintro; u1_buf_norm
    refine ⟨?_, by decide, by decide, by decide⟩
    u1_prefix_tac))

set_option hygiene false in
/-- A nested field's `Marshal` (its general form, `wp_Marshal_gen`), the field's points-to named
after the field. -/
macro "u1_mnest" : tactic => `(tactic| first
  | (wp_apply (state.Key.wp_Marshal_gen (E0 := E0)) $$ [Hw K] as ⟨Hw, K⟩
     iframe Hwr HQ Hw K; ipureintro; u1_prefix_tac)
  | (wp_apply (state.Key.wp_Marshal_gen (E0 := E0)) $$ [Hw Key] as ⟨Hw, Key⟩
     iframe Hwr HQ Hw Key; ipureintro; u1_prefix_tac)
  | (wp_apply (state.Value.wp_Marshal_gen (E0 := E0)) $$ [Hw V] as ⟨Hw, V⟩
     iframe Hwr HQ Hw V; ipureintro; u1_prefix_tac)
  | (wp_apply (state.Value.wp_Marshal_gen (E0 := E0)) $$ [Hw OldValue] as ⟨Hw, OldValue⟩
     iframe Hwr HQ Hw OldValue; ipureintro; u1_prefix_tac)
  | (wp_apply (state.Value.wp_Marshal_gen (E0 := E0)) $$ [Hw NewValue] as ⟨Hw, NewValue⟩
     iframe Hwr HQ Hw NewValue; ipureintro; u1_prefix_tac)
  | (wp_apply (state.Value.wp_Marshal_gen (E0 := E0)) $$ [Hw Value] as ⟨Hw, Value⟩
     iframe Hwr HQ Hw Value; ipureintro; u1_prefix_tac)
  | (wp_apply (state.Command.wp_Marshal_gen (E0 := E0)) $$ [Hw Command] as ⟨Hw, Command⟩
     iframe Hwr HQ Hw Command; ipureintro; u1_prefix_tac)
  | (wp_apply (gryffproto.ValTag.wp_Marshal_gen (E0 := E0)) $$ [Hw Vt] as ⟨Hw, Vt⟩
     iframe Hwr HQ Hw Vt; ipureintro; u1_prefix_tac)
  | (wp_apply (gryffproto.ValTag.wp_Marshal_gen (E0 := E0)) $$ [Hw Base] as ⟨Hw, Base⟩
     iframe Hwr HQ Hw Base; ipureintro; u1_prefix_tac)
  | (wp_apply (gryffproto.Dep.wp_Marshal_gen (E0 := E0)) $$ [Hw D] as ⟨Hw, D⟩
     iframe Hwr HQ Hw D; ipureintro; u1_prefix_tac))

set_option hygiene false in
/-- A load of an element of a `[5]int32` field (`Deps`, `CommittedDeps`). -/
macro "u1_wload_deps" : tactic => `(tactic| first
  | (wp_apply wp_load_arr32 $$ [Deps] as Deps; (iframe; ipureintro; try word); try wp_auto)
  | (wp_apply wp_load_arr32 $$ [CommittedDeps] as CommittedDeps
     (iframe; ipureintro; try word)
     try wp_auto))

set_option hygiene false in
/-- The body of a fixed-size `Marshal`: stores into `b`, its writes, nested `Marshal`s. -/
macro "u1_marshal_auto" : tactic => `(tactic|
  repeat (first | u1_wstore_b | u1_write_b | u1_mnest | u1_wload_deps | wp_auto))

set_option hygiene false in
/-- `Unmarshal`'s return of the error `err` (`Hne`, `Ha`), the struct's fields (split, `Hnn`)
put back together as `mk`. -/
macro "u1_ret_err" mk:term : tactic => `(tactic| (
  obtain ⟨ei, rfl⟩ : ∃ ei, err = interface.ok ei := by
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei => exact ⟨ei, rfl⟩
  try wp_auto
  try wp_for_post
  try simp only [List.append_assoc]
  iapply HΦ
  iright
  iframe Ha
  isplitr
  · ipureintro; exact Hne
  isplitr
  · ipureintro; exact Hwf
  iexists $mk, _
  iframe Hown
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe))

set_option hygiene false in
/-- `io.ReadAtLeast(wire, b[:k], k)` of `Unmarshal` into the local array `b`; its error returned
(the struct put back together as `mk`); the bytes read made a list literal. -/
macro "u1_read_b" mk:term : tactic => `(tactic| (
  (try simp only [sint_Z_W64_0, go.arrayIndexRef_0, w64_sub_zero, zero_val_arr_w8])
  wp_apply wp_wire_ReadAtLeast_arr $$ [Hown b] as %nr %err ⟨%data, Hown, Hr⟩
  (iframe Hrd Hown b; (try iframe Hpkg2 Hpkg3); ipureintro; refine ⟨by decide, by decide, by decide⟩)
  icases Hr with (⟨⟨%Hnil, %Hlen⟩, b⟩ | ⟨%Hne, #Ha, %Hwf, %vs', b⟩)
  rotate_left
  · u1_ret_err $mk
  subst Hnil
  rw [list_getD_eq data _ Hlen]
  (try word_lit_simp)
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.singleton_append, List.drop_succ_cons, List.drop_zero,
    List.replicate_succ, List.replicate_zero, Int.reduceToNat]
  try wp_auto))

set_option hygiene false in
/-- A load of a byte from the local array `b`. -/
macro "u1_wload_b" : tactic => `(tactic| (
  (try simp only [sint_Z_W64_0, go.arrayIndexRef_0, w64_sub_zero])
  wp_apply wp_load_byte_arr $$ [b] as b
  (iframe b; ipureintro; try word)
  (try simp only [List.getD_cons_zero, List.getD_cons_succ, Int.reduceToNat])
  try wp_auto))

set_option hygiene false in
/-- A nested field's `Unmarshal`, its error returned (the struct put back as `mk`). -/
macro "u1_unest" mk:term : tactic => `(tactic| first
  | (wp_apply state.Key.wp_Unmarshal_proof $$ [Hown K] as %err
       (⟨%Hnil, %_, -, K, Hown⟩ | ⟨%Hne, #Ha, %Hwf, %_, %_, K, Hown⟩)
     (iframe Hrd Hown K; iintro !> %D HI; iframe HI; ipureintro; trivial)
     rotate_left
     u1_ret_err $mk
     subst Hnil
     try wp_auto)
  | (wp_apply state.Key.wp_Unmarshal_proof $$ [Hown Key] as %err
       (⟨%Hnil, %_, -, Key, Hown⟩ | ⟨%Hne, #Ha, %Hwf, %_, %_, Key, Hown⟩)
     (iframe Hrd Hown Key; iintro !> %D HI; iframe HI; ipureintro; trivial)
     rotate_left
     u1_ret_err $mk
     subst Hnil
     try wp_auto)
  | (wp_apply state.Value.wp_Unmarshal_proof $$ [Hown V] as %err
       (⟨%Hnil, %_, -, V, Hown⟩ | ⟨%Hne, #Ha, %Hwf, %_, %_, V, Hown⟩)
     (iframe Hrd Hown V; iintro !> %D HI; iframe HI; ipureintro; trivial)
     rotate_left
     u1_ret_err $mk
     subst Hnil
     try wp_auto)
  | (wp_apply state.Value.wp_Unmarshal_proof $$ [Hown OldValue] as %err
       (⟨%Hnil, %_, -, OldValue, Hown⟩ | ⟨%Hne, #Ha, %Hwf, %_, %_, OldValue, Hown⟩)
     (iframe Hrd Hown OldValue; iintro !> %D HI; iframe HI; ipureintro; trivial)
     rotate_left
     u1_ret_err $mk
     subst Hnil
     try wp_auto)
  | (wp_apply state.Value.wp_Unmarshal_proof $$ [Hown NewValue] as %err
       (⟨%Hnil, %_, -, NewValue, Hown⟩ | ⟨%Hne, #Ha, %Hwf, %_, %_, NewValue, Hown⟩)
     (iframe Hrd Hown NewValue; iintro !> %D HI; iframe HI; ipureintro; trivial)
     rotate_left
     u1_ret_err $mk
     subst Hnil
     try wp_auto)
  | (wp_apply state.Value.wp_Unmarshal_proof $$ [Hown Value] as %err
       (⟨%Hnil, %_, -, Value, Hown⟩ | ⟨%Hne, #Ha, %Hwf, %_, %_, Value, Hown⟩)
     (iframe Hrd Hown Value; iintro !> %D HI; iframe HI; ipureintro; trivial)
     rotate_left
     u1_ret_err $mk
     subst Hnil
     try wp_auto)
  | (wp_apply state.Command.wp_Unmarshal_proof $$ [Hown Command] as %err
       (⟨%Hnil, %_, -, Command, Hown⟩ | ⟨%Hne, #Ha, %Hwf, %_, %_, Command, Hown⟩)
     (iframe Hrd Hown Command; iintro !> %D HI; iframe HI; ipureintro; trivial)
     rotate_left
     u1_ret_err $mk
     subst Hnil
     try wp_auto)
  | (wp_apply gryffproto.ValTag.wp_Unmarshal_proof $$ [Hown Vt] as %err
       (⟨%Hnil, %_, -, Vt, Hown⟩ | ⟨%Hne, #Ha, %Hwf, %_, %_, Vt, Hown⟩)
     (iframe Hrd Hown Vt; iintro !> %D HI; iframe HI; ipureintro; trivial)
     rotate_left
     u1_ret_err $mk
     subst Hnil
     try wp_auto)
  | (wp_apply gryffproto.ValTag.wp_Unmarshal_proof $$ [Hown Base] as %err
       (⟨%Hnil, %_, -, Base, Hown⟩ | ⟨%Hne, #Ha, %Hwf, %_, %_, Base, Hown⟩)
     (iframe Hrd Hown Base; iintro !> %D HI; iframe HI; ipureintro; trivial)
     rotate_left
     u1_ret_err $mk
     subst Hnil
     try wp_auto)
  | (wp_apply gryffproto.Dep.wp_Unmarshal_proof $$ [Hown D] as %err
       (⟨%Hnil, %_, -, D, Hown⟩ | ⟨%Hne, #Ha, %Hwf, %_, %_, D, Hown⟩)
     (iframe Hrd Hown D; iintro !> %D HI; iframe HI; ipureintro; trivial)
     rotate_left
     u1_ret_err $mk
     subst Hnil
     try wp_auto))

set_option hygiene false in
/-- The body of a fixed-size `Unmarshal`. -/
macro "u1_unmarshal_auto" mk:term : tactic => `(tactic|
  repeat (first | u1_read_b $mk | u1_wload_b | u1_wstore_deps | u1_unest $mk | wp_auto))

/-- The bytes read are the encoding of the decoded message (the decoding inverted). -/
macro "u1_dec_norm" : tactic => `(tactic| ((try word_lit_simp) <;> simp only [
  state.Key.enc, state.Value.enc, state.Command.enc, gryffproto.Tag.enc,
  gryffproto.ValTag.enc, gryffproto.Dep.enc, gryffproto.Read.enc, gryffproto.ReadReply.enc,
  gryffproto.Write.enc, gryffproto.WriteReply.enc, gryffproto.RMW.enc, gryffproto.RMWReply.enc,
  gryffproto.Read1Proxied.enc, gryffproto.Read1Reply.enc, gryffproto.Read2Proxied.enc, gryffproto.Read2Reply.enc,
  gryffproto.Write1Proxied.enc, gryffproto.Write1Reply.enc, gryffproto.Write2Proxied.enc, gryffproto.Write2Reply.enc,
  gryffproto.PreAccept.enc, gryffproto.PreAcceptReply.enc, gryffproto.EAccept.enc, gryffproto.ECommit.enc,
  gryffproto.TryPreAccept.enc, gryffproto.PrepareReply.enc, gryffproto.Executed.enc, gryffproto.PreAcceptOKReply.enc,
  gryffproto.AcceptOKReply.enc, epaxosproto.Prepare.enc, epaxosproto.PreAcceptOK.enc, epaxosproto.AcceptReply.enc,
  epaxosproto.CommitShort.enc, epaxosproto.TryPreAcceptReply.enc, clientproto.Ping.enc, clientproto.PingReply.enc,
  genericsmrproto.Beacon.enc, genericsmrproto.BeaconReply.enc, genericsmrproto.Propose.enc, genericsmrproto.ProposeReplyTS.enc,
  
  u32Le_dec, u64Le_dec, arrLe32, List.range_succ, List.range_zero, List.flatMap_append,
  List.flatMap_cons, List.flatMap_nil, Int.reduceToNat, List.getD_cons_zero, List.getD_cons_succ,
  List.cons_append, List.nil_append, List.append_assoc, List.singleton_append, List.append_nil]
  <;> rfl))

set_option hygiene false in
/-- A frozen `T.wp_Marshal` from its general form `gen` (`D = []`, `E0 = enc m`). -/
macro "u1_marshal_frozen" gen:term : tactic => `(tactic| (
  wp_start_folded as ⟨#Hwr, Hown, #HQ, Ht⟩
  ihave Hw := wst_init _ _ _ _ _ _ _ $$ Hown
  wp_apply ($gen (D := [])) $$ [Hw Ht] as ⟨Hw, Ht⟩
  · iframe Hwr HQ Hw Ht; ipureintro; simp
  iapply HΦ
  iunfold wst at Hw
  icases Hw with ⟨%k, %sent', %pend', %err', %H, Hown⟩
  iexists k, sent', pend', err'
  simp only [List.nil_append] at H
  iframe Ht Hown
  ipureintro; exact H))

end Perennial.gryff.wire
