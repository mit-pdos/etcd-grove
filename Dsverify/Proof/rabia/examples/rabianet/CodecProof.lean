/-
`Codec()` and `gens()` (kit.go) meet their specs `Codec.spec` and `gens.spec` (`KitModel.lean`;
notes/dsv-rabia.md; as paxos's `KitProof.lean` and remote's counter's `Codec.lean`):

* **The codec**: `EncIn` writes the put flag, then `putU64`'s 8 little-endian bytes of the key's
  length (`u64le`, `u64le_eq`: Perennial's `u64Le`) at 1..8 of a 9-byte slice, then appends the key
  and the value; `DecIn` reads them back (`getU64` decodes `u64Le`; a get's bytes end at the key,
  so its value is `""`); `EncOut`/`DecOut` a kind byte and the value; `IsRead`, `Unknown`,
  `IsUnknown`.
* **The generator**: `Gen(c, j)` is an input of the store (`inB`: an 8-byte key
  `"key0000"+digit`, a put's value `"v"+digit+digit`, never empty); `gens()`'s counters are a
  slice of `NC` `uint64`s in an invariant, each `atomic.AddUint64` opening it for one step.
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.ModelLemmas
public import Perennial.Proof.encoding.binary.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base
public import Perennial.Proof.sync.atomic.Results

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace rabia.examples.rabianet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote Perennial.rabia
  Perennial.rabia.model

section lemmas

open encoding.binary in
/-- `u64Le x`'s byte `i` is `byte(x >> (8*i))` (remote's counter's `Codec.lean`). -/
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

open encoding.binary in
/-- kit.go's bytes of a `uint64` are Perennial's `u64Le`. -/
theorem u64le_eq (x : w64) : u64le x = u64Le x := by
  rw [u64Le_8]
  simp only [u64le, List.range, List.range.loop, List.map_cons, List.map_nil]
  have h0 : x >>> W64 (8 * ((0 : Nat) : Int)) = x := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [h0]
  rfl

variable [GooseExts] [GoGlobalContext] in
open encoding.binary in
/-- An input's bytes: its flag, its key's length, its key, its value (a get's is `""`). -/
theorem encInB_shape (i : KIn) : ∃ (p : Bool) (k v : GoString),
    encInB i.1 = (if p then W8 1 else W8 0) :: (u64Le (W64 k.length) ++ k ++ v) ∧
    inVal i.1 = In.mk p k v ∧ k.length = 8 ∧ v.length < 2 ^ 40 := by
  rcases i with ⟨i, hi⟩
  cases i with
  | put k v =>
    refine ⟨true, k, v, ?_, rfl, hi.1.1, hi.2⟩
    simp [encInB, u64le_eq]
  | get k =>
    refine ⟨false, k, [], ?_, rfl, hi.1, by simp⟩
    simp [encInB, u64le_eq]

variable [GooseExts] [GoGlobalContext] in
/-- An output the codec encodes: its kind byte `c` (at most 3) decides its flags. -/
theorem outOk_shape (x : Out)
    (hx : (∃ o : KOut, x = outVal o.1) ∨ x = Out.mk true false false []) :
    ∃ c : w8, encOutB x = c :: x.V' ∧ uint.Z c ≤ 3 ∧
      x = Out.mk (decide (c = W8 3)) (decide (c = W8 2)) (decide (c = W8 1)) x.V' := by
  rcases hx with ⟨⟨o, _⟩, rfl⟩ | rfl
  · cases o with
    | done => exact ⟨W8 2, rfl, by word, by simp [outVal]⟩
    | got w =>
      cases w with
      | none => exact ⟨W8 0, rfl, by word, by simp [outVal]⟩
      | some y => exact ⟨W8 1, rfl, by word, by simp [outVal]⟩
  · exact ⟨W8 3, rfl, by word, by simp⟩

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : rabia.examples.rabianet.Assumptions]
variable [bvi : go.BasicIntoValInj]
variable [π : NetProtoGS] [ρ : RemoteGS]

local notation "kpkg" => pkg_id.rabia.examples.rabianet

set_option goose.wp.extras true

theorem wp_putU64 (b : GoSlice) (L : List w8) (hL : L.length = 8) (x : w64) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ b ↦* L }}
      (App (App (Val (@! rabia.examples.rabianet.putU64)) (Val #b)) (Val #x))
    {{ RET #(); b ↦* u64Le x }} := by
  wp_start as Hb
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  have hb8 : sint.Z b.len = 8 := by have := Hbl.1; rw [hL] at this; word
  wp_auto
  ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
      "Hb" ∷ b ↦* ((u64Le x).take (uint.nat j) ++ L.drop (uint.nat j)) ∗
      "%Hj" ∷ ⌜uint.nat j ≤ 8⌝ : IProp GF) $$ [i Hb]
  · iexists W64 0
    iframe
    ipureintro; simp
  wp_for HI
  wp_if_destruct
  · have hj8 : uint.nat j < 8 := by word
    have hj0 : 0 ≤ sint.Z j := by word
    have hjz : sint.Z j < 8 := by word
    have hs : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z b.len := ⟨hj0, by omega⟩
    rw [ite_eq_left hs]
    wp_apply wp_store_slice_index b (sint.Z j) _ (W8 (uint.Z (x >>> (W64 8 * j))))
      $$ [Hb] as Hb
    · have hlen : ((u64Le x).take (uint.nat j) ++ L.drop (uint.nat j)).length = 8 := by
        simp only [List.length_append, List.length_take, List.length_drop, u64Le_length, hL]
        omega
      iframe Hb; ipureintro; rw [hlen]; exact ⟨hs.1, by exact_mod_cast hjz⟩
    wp_for_post
    iframe
    iexists j + W64 1
    have hsn : (sint.Z j).toNat = uint.nat j := by word
    rw [hsn, take_drop_set (u64Le_getElem x j hj8) (by rw [hL]; word),
      show uint.nat (j + W64 1) = uint.nat j + 1 by word]
    iframe
    ipureintro; word
  · have hj8 : uint.nat j = 8 := by word
    rw [hj8, List.take_of_length_le (by simp [u64Le_length]), List.drop_of_length_le (by omega),
      List.append_nil]
    iapply HΦ
    iexact Hb

theorem wp_getU64 (b : GoSlice) (bs : List w8) (dq : DFrac) (h : 8 ≤ bs.length) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ b ↦*{dq} bs }}
      (App (Val (@! rabia.examples.rabianet.getU64)) (Val #b))
    {{ RET #(leToU64 (bs.take 8)); b ↦*{dq} bs }} := by
  wp_start as Hb
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  have hb8 : 8 ≤ sint.Z b.len := by
    have := Hbl.1
    have h2 : ((sint.nat b.len : Nat) : Int) = sint.Z b.len := Int.toNat_of_nonneg Hbl.2
    omega
  wp_auto
  ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
      "x" ∷ x_ptr ↦ leToU64 (bs.take (uint.nat j)) ∗
      "%Hj" ∷ ⌜uint.nat j ≤ 8⌝ : IProp GF) $$ [i x]
  · iexists W64 0
    iframe
    ipureintro; simp
  wp_for HI
  wp_if_destruct
  · have hj8 : uint.nat j < 8 := by word
    have hj0 : 0 ≤ sint.Z j := by word
    have hjz : sint.Z j < 8 := by word
    have hs : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z b.len := ⟨hj0, by omega⟩
    rw [ite_eq_left hs]
    have hsn : (sint.Z j).toNat = uint.nat j := by word
    obtain ⟨w, hw⟩ : ∃ w, bs[uint.nat j]? = some w :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_apply wp_load_slice_index b (sint.Z j) _ dq w hj0 $$ [Hb] as Hb
    · iframe Hb; ipureintro; rw [hsn]; exact hw
    wp_for_post
    iframe
    iexists j + W64 1
    rw [show uint.nat (j + W64 1) = uint.nat j + 1 by word, leToU64_take_succ bs j w hj8 hw]
    iframe
    ipureintro; word
  · have hj8 : uint.nat j = 8 := by word
    rw [hj8]
    iapply HΦ
    iexact Hb

theorem Codec.wp_proof : Codec.spec (GF := GF) (hG := hG) := by
  intro γ
  wp_start
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold codecOk kvR
  simp only
  isplitr
  · -- EncIn
    iintro %i
    iintro !> %Φ' - HΦ'
    rcases i with ⟨i, hi⟩
    cases i with
    | put k v =>
      simp only [inVal, encInB]
      wp_auto
      have hk8 : k.length = 8 := hi.1.1
      have hv : v.length < 2 ^ 40 := hi.2
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hv
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hv'
      wp_apply (wp_slice_make3 (V := w8) (W64 9) (W64 9 + W64 k.length + W64 v.length)
        (by rw [hk8]; word)) as %b ⟨Hb, Hcap, -⟩
      ihave %Hbl := ownSlice_len _ _ _ $$ Hb
      ihave %Hbw := ownSlice_wf _ _ _ $$ Hb
      have hb9 : sint.Z b.len = 9 := by
        have := Hbl.1; simp only [List.length_replicate] at this; word
      have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by rw [hb9]; decide
      rw [ite_eq_left h0]
      wp_apply wp_store_slice_index b (sint.Z (W64 0)) _ (W8 1) $$ [Hb] as Hb
      · iframe Hb; ipureintro; simp only [List.length_replicate]; word
      rw [show (List.replicate 9 (zero_val w8)).set 0 (W8 1) =
        W8 1 :: List.replicate 8 (W8 0) from rfl]
      have h1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len := by rw [hb9]; decide
      rw [ite_eq_left ⟨h1.1, h1.2, Hbw.2⟩]
      icases (ownSlice_split_all (W64 1) b _ _ h1).1 $$ Hb with ⟨Hb1, Hb2⟩
      rw [show sint.nat (W64 1) = 1 from rfl, List.take_one, List.drop_one, List.head?_cons,
        Option.toList_some, List.tail_cons]
      wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      wp_apply wp_putU64 (slice.slice b w8 (W64 1) b.len) (List.replicate 8 (W8 0)) (by simp)
        (W64 k.length) $$ [$Hb2] as Hb2
      ihave Hb := (ownSlice_split_all (W64 1) b (DFrac.own 1) (W8 1 :: u64Le (W64 k.length)) h1).2
        $$ [Hb1 Hb2]
      · rw [show sint.nat (W64 1) = 1 from rfl, List.take_one, List.drop_one, List.head?_cons,
          Option.toList_some, List.tail_cons]
        iframe Hb1 Hb2
      wp_apply wp_string_to_bytes as %sk ⟨Hsk, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsk] as %b2 ⟨Hb, Hcap, -⟩
      wp_apply wp_string_to_bytes as %sv ⟨Hsv, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsv] as %b3 ⟨Hb, -, -⟩
      iapply HΦ'
      rw [u64le_eq]
      simp only [List.cons_append, List.append_assoc]
      iexact Hb
    | get k =>
      simp only [inVal, encInB]
      wp_auto
      have hk8 : k.length = 8 := hi.1
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hv
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hv'
      wp_apply (wp_slice_make3 (V := w8) (W64 9) (W64 9 + W64 k.length + W64 ([] : GoString).length)
        (by simp only [hk8, List.length_nil]; word)) as %b ⟨Hb, Hcap, -⟩
      ihave %Hbl := ownSlice_len _ _ _ $$ Hb
      ihave %Hbw := ownSlice_wf _ _ _ $$ Hb
      have hb9 : sint.Z b.len = 9 := by
        have := Hbl.1; simp only [List.length_replicate] at this; word
      rw [show List.replicate 9 (zero_val w8) = W8 0 :: List.replicate 8 (W8 0) from rfl]
      have h1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len := by rw [hb9]; decide
      rw [ite_eq_left ⟨h1.1, h1.2, Hbw.2⟩]
      icases (ownSlice_split_all (W64 1) b _ _ h1).1 $$ Hb with ⟨Hb1, Hb2⟩
      rw [show sint.nat (W64 1) = 1 from rfl, List.take_one, List.drop_one, List.head?_cons,
        Option.toList_some, List.tail_cons]
      wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      wp_apply wp_putU64 (slice.slice b w8 (W64 1) b.len) (List.replicate 8 (W8 0)) (by simp)
        (W64 k.length) $$ [$Hb2] as Hb2
      ihave Hb := (ownSlice_split_all (W64 1) b (DFrac.own 1) (W8 0 :: u64Le (W64 k.length)) h1).2
        $$ [Hb1 Hb2]
      · rw [show sint.nat (W64 1) = 1 from rfl, List.take_one, List.drop_one, List.head?_cons,
          Option.toList_some, List.tail_cons]
        iframe Hb1 Hb2
      wp_apply wp_string_to_bytes as %sk ⟨Hsk, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsk] as %b2 ⟨Hb, Hcap, -⟩
      wp_apply wp_string_to_bytes as %sv ⟨Hsv, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsv] as %b3 ⟨Hb, -, -⟩
      iapply HΦ'
      rw [u64le_eq]
      simp only [List.cons_append, List.append_assoc, List.append_nil]
      iexact Hb
  isplitr
  · -- DecIn
    iintro %i %b %dq
    iintro !> %Φ' Hb HΦ'
    obtain ⟨p, k, v, he, hin, hk8, hv⟩ := encInB_shape i
    have hiv : inV i.1 = interface.mkOk In.ty #(In.mk p k v) := by
      show interface.mkOk In.ty #(inVal i.1) = _; rw [hin]
    rw [he, hiv]
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    ihave %Hbw := ownSlice_wf _ _ _ $$ Hb
    have hbl : sint.Z b.len = 9 + k.length + v.length := by
      obtain ⟨h1, h2⟩ := Hlen
      simp only [List.length_cons, List.length_append, u64Le_length] at h1
      have h3 : ((sint.nat b.len : Nat) : Int) = sint.Z b.len := Int.toNat_of_nonneg h2
      omega
    wp_auto
    have h9 : ¬ sint.Z b.len < sint.Z (W64 9) := by
      rw [hbl, show sint.Z (W64 9) = 9 from rfl]; omega
    rw [decide_eq_false h9]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by
      rw [hbl, show sint.Z (W64 0) = 0 from rfl]; omega
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if p then W8 1 else W8 0) (by decide)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_if_destruct
    · exfalso; cases p <;> simp only [Bool.false_eq_true, ↓reduceIte] at Hif <;> word
    have h1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len := by
      rw [hbl, show sint.Z (W64 1) = 1 from rfl]; omega
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len ∧
      sint.Z b.len ≤ sint.Z b.cap from ⟨h1.1, h1.2, Hbw.2⟩)]
    icases (ownSlice_split_all (W64 1) b _ _ h1).1 $$ Hb with ⟨Hb1, Hb2⟩
    rw [show sint.nat (W64 1) = 1 from rfl, List.take_one, List.drop_one, List.head?_cons,
      Option.toList_some, List.tail_cons]
    wp_apply wp_getU64 _ _ dq (by simp [u64Le_length]) $$ [$Hb2] as Hb2
    ihave Hb := (ownSlice_split_all (W64 1) b dq
      ((if p then W8 1 else W8 0) :: (u64Le (W64 k.length) ++ k ++ v)) h1).2 $$ [Hb1 Hb2]
    · rw [show sint.nat (W64 1) = 1 from rfl, List.take_one, List.drop_one, List.head?_cons,
        Option.toList_some, List.tail_cons]
      iframe Hb1 Hb2
    rw [List.append_assoc, List.take_left' (by simp [u64Le_length]), u64Le_to_word]
    have hn : ¬ uint.Z (b.len - W64 9) < uint.Z (W64 (k.length : Int)) := by
      rw [hk8]; rw [hk8] at hbl; word
    rw [decide_eq_false hn]
    wp_auto
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq (if p then W8 1 else W8 0) (by decide)
      $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    have hkw : sint.Z (W64 9 + W64 (k.length : Int)) = 17 := by rw [hk8]; rfl
    have hs1 : 0 ≤ sint.Z (W64 9) ∧ sint.Z (W64 9) ≤ sint.Z (W64 9 + W64 (k.length : Int)) ∧
        sint.Z (W64 9 + W64 (k.length : Int)) ≤ sint.Z b.cap := by
      rw [hkw, show sint.Z (W64 9) = 9 from rfl]; omega
    rw [ite_eq_left hs1]
    have hL : ((if p then W8 1 else W8 0) :: (u64Le (W64 (k.length : Int)) ++ (k ++ v))) =
        ((if p then W8 1 else W8 0) :: u64Le (W64 (k.length : Int))) ++ k ++ v := by simp
    have h3 := list_slice3 ((if p then W8 1 else W8 0) :: u64Le (W64 (k.length : Int))) k v 9 17
      (by simp [u64Le_length]) (by rw [hk8]) (by omega)
    rw [hL]
    icases (ownSlice_slice (W64 9) (W64 9 + W64 (k.length : Int)) b dq _
      ⟨hs1.1, hs1.2.1, by rw [hkw, hbl]; omega⟩).1 $$ Hb with ⟨Hb1, Hb2, Hb3⟩
    rw [show sint.nat (W64 9) = 9 from rfl, show sint.nat (W64 9 + W64 (k.length : Int)) = 17 by
      rw [hk8]; rfl, h3.1, h3.2.1, h3.2.2]
    wp_apply wp_bytes_to_string $$ [Hb2] as Hb2
    · iexact Hb2
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 9 + W64 (k.length : Int)) ∧
      sint.Z (W64 9 + W64 (k.length : Int)) ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.cap from
      ⟨by rw [hkw]; omega, by rw [hkw, hbl]; omega, Hbw.2⟩)]
    wp_apply wp_bytes_to_string $$ [Hb3] as Hb3
    · iexact Hb3
    iapply HΦ'
    ipureintro
    intro _
    cases p <;> rfl
  isplitr
  · -- EncOut
    iintro %v %Hv
    obtain ⟨x, rfl, hx⟩ : ∃ x : Out, v = interface.mkOk Out.ty #x ∧ x.V'.length + 9 < 2 ^ 63 := by
      rcases Hv with ⟨o, h⟩ | ⟨_, h⟩
      · exact ⟨_, h, outVal_len o⟩
      · exact ⟨_, h, by simp⟩
    iintro !> %Φ' - HΦ'
    rw [encOutV_out x hx]
    rcases x with ⟨u, pt, f, w⟩
    simp only at hx
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    wp_apply (wp_slice_make3 (V := w8) (W64 1) (W64 1 + W64 w.length) (by word))
      as %b ⟨Hb, Hcap, -⟩
    ihave %Hbl := ownSlice_len _ _ _ $$ Hb
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by
      obtain ⟨h1, h2⟩ := Hbl; simp only [List.length_replicate] at h1; word
    rw [show List.replicate 1 (zero_val w8) = [W8 0] from rfl]
    cases u
    · cases pt
      · cases f
        · wp_auto
          wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
          wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', -, -⟩
          iapply HΦ'
          simp only [encOutB, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
            List.cons_append, List.nil_append, List.set_cons_zero]
          iexact Hb'
        · wp_auto
          rw [ite_eq_left h0]
          wp_apply wp_store_slice_index b (sint.Z (W64 0)) _ (W8 1) $$ [Hb] as Hb
          · iframe Hb; ipureintro; simp
          wp_auto
          wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
          wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', -, -⟩
          iapply HΦ'
          simp only [encOutB, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
            List.cons_append, List.nil_append, List.set_cons_zero]
          iexact Hb'
      · wp_auto
        rw [ite_eq_left h0]
        wp_apply wp_store_slice_index b (sint.Z (W64 0)) _ (W8 2) $$ [Hb] as Hb
        · iframe Hb; ipureintro; simp
        wp_auto
        wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
        wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', -, -⟩
        iapply HΦ'
        simp only [encOutB, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
          List.cons_append, List.nil_append, List.set_cons_zero]
        iexact Hb'
    · wp_auto
      rw [ite_eq_left h0]
      wp_apply wp_store_slice_index b (sint.Z (W64 0)) _ (W8 3) $$ [Hb] as Hb
      · iframe Hb; ipureintro; simp
      wp_auto
      wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append (V := w8) $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb', -, -⟩
      iapply HΦ'
      simp only [encOutB, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
        List.cons_append, List.nil_append, List.set_cons_zero]
      iexact Hb'
  isplitr
  · -- DecOut
    iintro %v %b %dq %Hv
    obtain ⟨x, rfl, hx, hxs⟩ : ∃ x : Out, v = interface.mkOk Out.ty #x ∧
        x.V'.length + 9 < 2 ^ 63 ∧
        ((∃ o : KOut, x = outVal o.1) ∨ x = Out.mk true false false []) := by
      rcases Hv with ⟨o, h⟩ | ⟨_, h⟩
      · exact ⟨_, h, outVal_len o, .inl ⟨o, rfl⟩⟩
      · exact ⟨_, h, by simp, .inr rfl⟩
    obtain ⟨c, hc, hc3, hcx⟩ := outOk_shape x hxs
    iintro !> %Φ' Hb HΦ'
    rw [encOutV_out x hx, hc]
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    have hb1 : 1 ≤ sint.Z b.len := by
      obtain ⟨h1, h2⟩ := Hlen; simp only [List.length_cons] at h1
      have h3 : ((sint.nat b.len : Nat) : Int) = sint.Z b.len := Int.toNat_of_nonneg h2
      omega
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len := by
      constructor <;> word
    wp_auto
    have hl1 : ¬ sint.Z b.len < sint.Z (W64 1) := by
      rw [show sint.Z (W64 1) = 1 from rfl]; omega
    rw [decide_eq_false hl1]
    wp_auto
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq c (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_if_destruct
    · exfalso; word
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq c (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq c (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    rw [ite_eq_left h0]
    wp_apply wp_load_slice_index b (sint.Z (W64 0)) _ dq c (by word) $$ [Hb] as Hb
    · iframe Hb; ipureintro; rfl
    wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len ∧
      sint.Z b.len ≤ sint.Z b.cap from ⟨by word, by word, Hwf.2⟩)]
    icases (ownSlice_split_all (W64 1) b dq _ ⟨by word, by word⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
    rw [show sint.nat (W64 1) = 1 from rfl, List.drop_one, List.tail_cons]
    wp_apply wp_bytes_to_string $$ [Hb2] as Hb2
    · iexact Hb2
    iapply HΦ'
    ipureintro
    intro _
    exact (congrArg (fun y : Out => interface.mkOk Out.ty #y) hcx).symm
  isplitr
  · -- IsRead
    iintro %i
    iintro !> %Φ' - HΦ'
    rcases i with ⟨i, hi⟩
    cases i with
    | put k v =>
      simp only [inV, inVal]
      wp_auto
      rw [show (!kvB.isWrite ⟨KvInput.put k v, hi⟩) = false from rfl]
      iapply HΦ'
      itrivial
    | get k =>
      simp only [inV, inVal]
      wp_auto
      rw [show (!kvB.isWrite ⟨KvInput.get k, hi⟩) = true from rfl]
      iapply HΦ'
      itrivial
  isplitr
  · -- Unknown
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial
  isplitr
  · -- IsUnknown, an output
    iintro %o
    iintro !> %Φ' - HΦ'
    wp_auto
    rw [outVal_unknown o]
    iapply HΦ'
    itrivial
  · -- IsUnknown, an unknown output
    iintro %i
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial

/-! ## The generator -/

theorem wp_mix (c r : w64) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (App (Val (@! rabia.examples.rabianet.mix)) (Val #c)) (Val #r))
    {{ (x : w64), RET #x; True }} := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

theorem wp_digit (n : w64) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! rabia.examples.rabianet.digit)) (Val #n))
    {{ (s : GoString), RET #s; ⌜s.length = 1⌝ }} := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := w8) (t := go.byte) _
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, _⟩
  wp_apply wp_bytes_to_string $$ Hsl as Hsl
  iapply HΦ
  ipureintro; rfl

theorem wp_Gen (c j : w64) :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (App (Val (@! rabia.examples.rabianet.Gen)) (Val #c)) (Val #j))
    {{ (x : In), RET #x; ⌜∃ i : KIn, x = inVal i.1⌝ }} := by
  wp_start
  wp_auto
  wp_apply wp_mix as %m -
  wp_apply wp_digit as %d %hd
  have hk : ([107#8, 101#8, 121#8, 48#8, 48#8, 48#8, 48#8] ++ d : GoString).length = 8 := by
    simp [hd]
  wp_if_destruct
  · wp_apply wp_digit as %d1 %hd1
    wp_apply wp_digit as %d2 %hd2
    iapply HΦ
    ipureintro
    refine ⟨⟨.put _ _, ⟨⟨hk, by simp⟩, by simp [valLen, hd1, hd2]⟩⟩, rfl⟩
  · iapply HΦ
    ipureintro
    exact ⟨⟨.get _, ⟨hk, by simp [valLen]⟩⟩, rfl⟩

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The namespace of `gens()`'s counters' invariant. -/
def gensN : Namespace := nroot.@"rabianet_gens"

theorem gens.wp_proof : gens.spec (GF := GF) (hG := hG) := by
  wp_start
  simp only [NC]
  wp_auto
  wp_apply +noauto wp_slice_make2 (V := w64) (W64 6) $$ [] as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have hsl6 : sint.Z sl.len = 6 := by
    have := Hsll.1; simp only [List.length_replicate] at this; word
  iapply fupd_wp
  imod (inv_alloc gensN ⊤ (iprop(∃ vs : List w64, sl ↦* vs ∗ ⌜vs.length = 6⌝) : IProp GF))
    $$ [Hsl] with #Hinv
  · inext; iexists _; iframe Hsl; ipureintro; simp
  imodintro
  iapply wp_fupd
  wp_auto
  ipersist next
  imodintro
  iapply HΦ
  unfold lintest.genSpec
  iintro %id
  iintro !> %Φ' %Hid HΦ'
  have : sync.atomic.Assumptions := Assumptions.import_atomic_Assumption
  ihave #Hap : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z id < sint.Z (W64 0) by
    rw [show sint.Z (W64 0) = 0 from rfl]; omega)]
  wp_auto
  wp_if_destruct
  · wp_apply wp_Gen as %x %hx
    iapply HΦ'
    imodintro
    ipureintro
    obtain ⟨i, rfl⟩ := hx
    exact ⟨i, rfl⟩
  · have hb : 0 ≤ sint.Z id ∧ sint.Z id < sint.Z sl.len := by
      refine ⟨Hid, ?_⟩; rw [hsl6]; word
    rw [ite_eq_left hb]
    wp_auto
    wp_apply_core (sync.atomic.wp_AddUint64 (sliceIndexRef w64 (sint.Z id) sl) (W64 1))
      $$ [] [-Hap]
    · iexact Hap
    iinv Hinv with Hi Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    icases Hi with ⟨%vs, Hvs, %Hvl⟩
    obtain ⟨w, hw⟩ : ∃ w, vs[(sint.Z id).toNat]? = some w :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hvl]; word)⟩
    icases (ownSlice_elem_acc (sint.Z id) w sl _ vs Hid hw) $$ Hvs with ⟨Hw, Hback⟩
    iexists w
    iframe Hw
    iintro Hw
    imod Hmask with -
    imod Hclose $$ [Hw Hback] with -
    · inext
      iexists vs.set (sint.Z id).toNat (w + W64 1)
      isplitl [Hw Hback]
      · iapply Hback $$ Hw
      · ipureintro; simp [Hvl]
    imodintro
    wp_auto
    wp_apply wp_Gen as %x %hx
    iapply HΦ'
    imodintro
    ipureintro
    obtain ⟨i, rfl⟩ := hx
    exact ⟨i, rfl⟩

end proof

end rabia.examples.rabianet
end Perennial
