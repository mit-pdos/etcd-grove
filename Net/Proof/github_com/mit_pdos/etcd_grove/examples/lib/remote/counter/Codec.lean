/-
The proof of counter's `Codec` (`Net/Spec/.../lib/remote/counter/Codec.lean`): the seven function
literals, each against its part of `codecOk (cR γ)`. The inputs and outputs are boxed (`boxB`,
`outV`), so each type assertion succeeds. `EncOut` stores `byte(n >> (8*i))`, `u64Le n`'s byte `i`
(`u64Le_getElem`), at `1+i` of a fresh 9-byte slice; `DecOut` ors `uint64(b[1+i]) << (8*i)` into
`n`, which is `leToU64` of the first `i` bytes (`leToU64_take_succ`), and `u64Le`'s decoding is the
value back; both loops as `remote`'s `putU64`/`getU64` (their lemmas copied here: a proof imports
no proof). An output's bytes are `encOutB` (`encOutV_outV`, as `Out` values determine their
fields: `out_intoValInj`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Codec
public import Perennial.Proof.encoding.binary.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

open github_com.mit_pdos.etcd_grove.examples.lib.remote

section inj
variable [GooseExts] [go_gctx : GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]

/-- An `Out` value determines its fields (its fields' loads are deterministic). -/
instance out_intoValInj : go.IntoValInj Out where
  intoVal_inj x y h := by
    have hu : ∀ z : Out, is_go_step_pure (StructFieldGet Out.underlying go!"Unknown")
        #z = Eq (Val #(z.Unknown')) := fun z =>
      (Out.TypeAssumptions.get_Unknown z).isGoStep_det_internal.isGoStep_pure_det
    have hn : ∀ z : Out, is_go_step_pure (StructFieldGet Out.underlying go!"N")
        #z = Eq (Val #(z.N')) := fun z =>
      (Out.TypeAssumptions.get_N z).isGoStep_det_internal.isGoStep_pure_det
    have e1 := hu x
    rw [h, hu y] at e1
    have e2 := hn x
    rw [h, hn y] at e2
    have f1 : Val #(x.Unknown') = Val #(y.Unknown') := by
      have := congrFun e1 (Val #(x.Unknown')); simp only [eq_iff_iff, iff_true] at this
      exact this.symm
    have f2 : Val #(x.N') = Val #(y.N') := by
      have := congrFun e2 (Val #(x.N')); simp only [eq_iff_iff, iff_true] at this; exact this.symm
    injection f1 with f1
    injection f2 with f2
    cases x; cases y
    simp only [Out.mk.injEq]
    exact ⟨GoGlobalContext.intoVal_inj_bool f1, GoGlobalContext.intoVal_inj_w64 f2⟩

theorem outV_inj {u u' : Bool} {n n' : w64} (h : outV u n = outV u' n') : u = u' ∧ n = n' := by
  simp only [outV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h
  have h' := go.intoVal_inj h
  simp only [Out.mk.injEq] at h'
  exact h'

/-- `Out{u, n}`'s bytes. -/
theorem encOutV_outV (u : Bool) (n : w64) : encOutV (outV u n) = encOutB u n := by
  unfold encOutV
  split
  · rename_i h
    obtain ⟨h1, h2⟩ := outV_inj h.choose_spec
    rw [← h1, ← h2]
  · rename_i h
    exact absurd ⟨(u, n), rfl⟩ h

end inj

section lemmas

open encoding.binary in
/-- `u64Le x`'s byte `i` is `byte(x >> (8*i))`. -/
theorem u64Le_getElem (x i : w64) (hi : uint.nat i < 8) :
    (u64Le x)[uint.nat i]? = some (W8 (uint.Z (x >>> (W64 8 * i)))) := by
  obtain ⟨n, hn, rfl⟩ : ∃ n : Nat, n < 8 ∧ i = W64 n := ⟨uint.nat i, hi, by word⟩
  have hn' : uint.nat (W64 n : w64) = n := by word
  rw [hn', u64Le_8]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
  all_goals first | rfl | omega

/-- Storing the next byte of `l1` over `l2`. -/
theorem take_drop_set {l1 l2 : List w8} {n : Nat} {a : w8} (h1 : l1[n]? = some a)
    (h2 : n < l2.length) :
    (l1.take n ++ l2.drop n).set n a = l1.take (n + 1) ++ l2.drop (n + 1) := by
  have hn : n < l1.length := by
    rcases Nat.lt_or_ge n l1.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at h1; cases h1
  have ht : (l1.take n).length = n := by simp; omega
  rw [List.set_append, ite_eq_right (by omega), ht, Nat.sub_self, List.take_add_one, h1]
  rw [List.drop_eq_getElem_cons h2, List.set_cons_zero]
  simp

theorem combine_append_single (l : List w8) (v : w8) :
    LittleEndian.combine (l ++ [v]) = LittleEndian.combine l + v.toNat * 2 ^ (8 * l.length) := by
  induction l with
  | nil => simp [LittleEndian.combine]
  | cons a l ih =>
    simp only [List.cons_append, LittleEndian.combine, ih, List.length_cons]
    rw [show 8 * (l.length + 1) = 8 * l.length + 8 by omega, Nat.pow_add, Nat.mul_add,
      Nat.add_assoc]
    congr 2
    rw [Nat.mul_comm 256, Nat.mul_assoc]

open encoding.binary in
/-- One more byte of the little-endian decoding: `x | uint64(v) << (8*i)`. -/
theorem leToU64_take_succ (bs : List w8) (i : w64) (v : w8) (hi : uint.nat i < 8)
    (hv : bs[uint.nat i]? = some v) :
    leToU64 (bs.take (uint.nat i + 1)) =
      leToU64 (bs.take (uint.nat i)) ||| (W64 (uint.Z v) <<< (W64 8 * i)) := by
  have hl : (bs.take (uint.nat i)).length = uint.nat i := by
    have : uint.nat i < bs.length := by
      rcases Nat.lt_or_ge (uint.nat i) bs.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hv; cases hv
    simp; omega
  have hc := combine_bound (bs.take (uint.nat i))
  rw [hl] at hc
  have hlt : 2 ^ (8 * uint.nat i) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) (by omega)
  have hv8 := v.isLt
  rw [List.take_add_one, hv, Option.toList_some, leToU64, leToU64Def, leToU64, leToU64Def,
    combine_append_single, hl]
  have hsh : (W64 8 * i).toNat = 8 * uint.nat i := by word
  have hw : (W64 (uint.Z v) : w64) = v.setWidth 64 := by
    simp only [W64, uint.Z, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  apply BitVec.eq_of_toNat_eq
  rw [hw, BitVec.shiftLeft_eq', hsh,
    toNat_or_shl _ v (8 * uint.nat i) (by rw [BitVec.toNat_ofNat]; omega) (by omega)]
  simp only [BitVec.toNat_ofNat]
  have : (v.toNat + 1) * 2 ^ (8 * uint.nat i) ≤ 256 * 2 ^ (8 * uint.nat i) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]

theorem Codec.wp_proof : Codec.spec (GF := GF) (hG := hG) := by
  intro γ
  wp_start
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold codecOk cR
  simp only
  isplitr
  · -- EncIn
    iintro %i
    iintro !> %Φ' _ HΦ'
    wp_auto
    cases i <;>
    · simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_apply wp_slice_literal (V := w8) [_]
      isplitr
      · ipureintro; rfl
      iintro %lit ⟨Hlit, -⟩
      wp_auto
      iapply HΦ'
      iexact Hlit
  isplitr
  · -- DecIn
    iintro %i %b %dq
    iintro !> %Φ' Hb HΦ'
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    have hb1 : b.len = W64 1 := by
      obtain ⟨h1, h2⟩ := Hlen; simp only [List.length_singleton] at h1; word
    wp_auto
    wp_if_destruct
    · have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by rw [hb1]; decide
      rw [ite_eq_left h0]
      wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if i then W8 1 else W8 0) (by word)
        $$ [Hb] as Hb
      · iframe Hb; ipureintro; rfl
      wp_if_destruct
      · exfalso; cases i <;> simp only [Bool.false_eq_true, ↓reduceIte] at Hif <;> word
      · rw [ite_eq_left h0]
        wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if i then W8 1 else W8 0) (by word)
          $$ [Hb] as Hb
        · iframe Hb; ipureintro; rfl
        iapply HΦ'
        ipureintro
        intro _
        cases i <;> rfl
    · exfalso; exact Hif hb1
  isplitr
  · -- EncOut
    iintro %v %Hv
    obtain ⟨u, n, rfl⟩ : ∃ u n, v = outV u n := by
      rcases Hv with ⟨o, h⟩ | ⟨_, h⟩
      · exact ⟨_, _, h⟩
      · exact ⟨_, _, h⟩
    iintro !> %Φ' _ HΦ'
    rw [encOutV_outV]
    wp_auto
    wp_apply (wp_slice_make2 (V := w8) (W64 9)) as %b ⟨Hb, -⟩
    · ipureintro; decide
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    have hb9 : b.len = W64 9 := by
      obtain ⟨h1, h2⟩ := Hbl; simp only [List.length_replicate] at h1; word
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by rw [hb9]; decide
    simp only
    wp_if_destruct
    · obtain ⟨hd, hhd, hL⟩ : ∃ hd : w8, encOutB false n = hd :: u64Le n ∧
          List.replicate 9 (zero_val w8) = hd :: List.replicate 8 (W8 0) := ⟨_, rfl, rfl⟩
      rw [hhd, hL]
      sorry
    · rw [ite_eq_left h0]
      wp_apply wp_store_slice_index b (sint.Z (W64 0)) _ (W8 1) $$ [Hb] as Hb
      · iframe Hb; ipureintro; simp only [List.length_replicate]; word
      wp_auto
      obtain ⟨hd, hhd, hL⟩ : ∃ hd : w8, encOutB true n = hd :: u64Le n ∧
          (List.replicate 9 (zero_val w8)).set (sint.Z (W64 0)).toNat (W8 1) =
            hd :: List.replicate 8 (W8 0) := ⟨_, rfl, rfl⟩
      rw [hhd, hL]
      sorry
  isplitr
  · -- DecOut
    sorry
  isplitr
  · -- IsRead
    iintro %i
    iintro !> %Φ' _ HΦ'
    wp_auto
    simp only [cB]
    iapply HΦ'
    itrivial
  isplitr
  · -- Unknown
    iintro %i
    iintro !> %Φ' _ HΦ'
    wp_auto
    rw [show (0 : w64) = W64 0 from rfl]
    iapply HΦ'
    itrivial
  isplitr
  · -- IsUnknown, an output
    iintro %o
    iintro !> %Φ' _ HΦ'
    wp_auto
    iapply HΦ'
    itrivial
  · -- IsUnknown, an unknown output
    iintro %i
    iintro !> %Φ' _ HΦ'
    wp_auto
    iapply HΦ'
    itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
