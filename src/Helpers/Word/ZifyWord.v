(** * [zify] support for the fixed-width words [w8], [w16], [w32], [w64].

    These instances teach [zify] (and so [lia]) about [uint.Z], [sint.Z],
    [word.of_Z], the arithmetic and bitwise word operations, and equality at
    word type, for Perennial's four concrete word instances. With them,
    [zify] translates a goal about words into a goal about [Z] in a single
    OCaml pass; the [word] tactic (Automation.v) is built on this.

    Modular wrapping is expressed with [wrapZ] rather than a bare [Z.modulo],
    so that its [BinOpSpec] -- the Euclidean-division equations [lia] needs --
    attaches only to the wraps this file produces and not to every [mod] in
    the world. The quotient in that spec is written as the term [z / m]: [lia]
    treats it as an opaque atom, which is exactly a fresh quotient variable,
    and [Z.div_mod_to_equations] is then not needed.

    This follows [Stdlib.micromega.ZifyUint63] closely. The per-width blocks
    below are identical except for the numbers; the generic lemmas are stated
    once, in [Section generic], with the width-specific literals as explicit
    arguments, because [zify] needs the instance bodies to be literal records
    (it reads them by reduction) and needs concrete literals, not [2^width]. *)

From Coq Require Import ZArith Lia.
From stdpp Require Import prelude.
From Stdlib.micromega Require Import ZifyClasses.
From coqutil.Word Require Import Interface Properties.
From Perennial.Helpers.Word Require Import Integers.

Local Open Scope Z_scope.

Definition wrapZ (m z : Z) : Z := z mod m.

Lemma wrapZ_spec m z : 0 < m → 0 ≤ wrapZ m z < m ∧ wrapZ m z = z - m * (z / m).
Proof.
  intros. unfold wrapZ. split; [ apply Z.mod_pos_bound; lia | apply Z.mod_eq; lia ].
Qed.

#[global] Instance wrapZ_BinOpSpec : BinOpSpec wrapZ :=
  { BPred m z r := 0 < m → 0 ≤ r < m ∧ r = z - m * (z / m); BSpec := wrapZ_spec }.
Add Zify BinOpSpec wrapZ_BinOpSpec.

Section generic.
Context {width : Z} {word : Interface.word width} {word_ok : word.ok word}.
Implicit Types (x y : word).

Lemma zw_range wB (HwB : wB = 2^width) x : 0 ≤ uint.Z x < wB.
Proof. subst. apply word.unsigned_range. Qed.

Lemma zw_signed wB half (HwB : wB = 2^width) (Hhalf : half = 2^(width-1)) x :
  sint.Z x = wrapZ wB (uint.Z x + half) - half.
Proof. subst. rewrite word.signed_eq_swrap_unsigned. reflexivity. Qed.

Lemma zw_of_Z wB (HwB : wB = 2^width) z : uint.Z (@word.of_Z width word z) = wrapZ wB z.
Proof. subst. rewrite word.unsigned_of_Z. reflexivity. Qed.

Lemma zw_add wB (HwB : wB = 2^width) x y : uint.Z (word.add x y) = wrapZ wB (uint.Z x + uint.Z y).
Proof. subst. rewrite word.unsigned_add. reflexivity. Qed.

Lemma zw_sub wB (HwB : wB = 2^width) x y : uint.Z (word.sub x y) = wrapZ wB (uint.Z x - uint.Z y).
Proof. subst. rewrite word.unsigned_sub. reflexivity. Qed.

Lemma zw_mul wB (HwB : wB = 2^width) x y : uint.Z (word.mul x y) = wrapZ wB (uint.Z x * uint.Z y).
Proof. subst. rewrite word.unsigned_mul. reflexivity. Qed.

Lemma zw_opp wB (HwB : wB = 2^width) x : uint.Z (word.opp x) = wrapZ wB (- uint.Z x).
Proof. subst. rewrite word.unsigned_opp. reflexivity. Qed.

Lemma zw_or wB (HwB : wB = 2^width) x y : uint.Z (word.or x y) = wrapZ wB (Z.lor (uint.Z x) (uint.Z y)).
Proof. subst. rewrite word.unsigned_or. reflexivity. Qed.

Lemma zw_and wB (HwB : wB = 2^width) x y : uint.Z (word.and x y) = wrapZ wB (Z.land (uint.Z x) (uint.Z y)).
Proof. subst. rewrite word.unsigned_and. reflexivity. Qed.

Lemma zw_xor wB (HwB : wB = 2^width) x y : uint.Z (word.xor x y) = wrapZ wB (Z.lxor (uint.Z x) (uint.Z y)).
Proof. subst. rewrite word.unsigned_xor. reflexivity. Qed.

Lemma zw_not wB (HwB : wB = 2^width) x : uint.Z (word.not x) = wrapZ wB (Z.lnot (uint.Z x)).
Proof. subst. rewrite word.unsigned_not. reflexivity. Qed.

Lemma zw_ndn wB (HwB : wB = 2^width) x y : uint.Z (word.ndn x y) = wrapZ wB (Z.ldiff (uint.Z x) (uint.Z y)).
Proof. subst. rewrite word.unsigned_ndn. reflexivity. Qed.

Lemma zw_eq x y : x = y ↔ uint.Z x = uint.Z y.
Proof. split; [ intros -> | apply word.unsigned_inj ]; reflexivity. Qed.
End generic.

(** ** 8-bit words. Not in a [Section]: [Add Zify] registrations do not
    survive [End Section]. *)

#[global] Instance Inj_w8 : InjTyp (@word.rep 8 w8_word_instance) Z :=
  mkinj _ _ uint.Z (fun z => 0 ≤ z < 256) (@zw_range 8 _ _ 256 eq_refl).
Add Zify InjTyp Inj_w8.

#[global] Instance Op_w8_unsigned : UnOp (@word.unsigned 8 w8_word_instance) :=
  { TUOp := fun z => z; TUOpInj := fun _ => eq_refl }.
Add Zify UnOp Op_w8_unsigned.

#[global] Instance Op_w8_signed : UnOp (@word.signed 8 w8_word_instance) :=
  { TUOp := fun z => wrapZ 256 (z + 128) - 128; TUOpInj := @zw_signed 8 _ _ 256 128 eq_refl eq_refl }.
Add Zify UnOp Op_w8_signed.

#[global] Instance Op_w8_of_Z : UnOp (@word.of_Z 8 w8_word_instance) :=
  { TUOp := wrapZ 256; TUOpInj := @zw_of_Z 8 _ _ 256 eq_refl }.
Add Zify UnOp Op_w8_of_Z.

#[global] Instance Op_w8_add : BinOp (@word.add 8 w8_word_instance) :=
  { TBOp := fun x y => wrapZ 256 (x + y); TBOpInj := @zw_add 8 _ _ 256 eq_refl }.
Add Zify BinOp Op_w8_add.

#[global] Instance Op_w8_sub : BinOp (@word.sub 8 w8_word_instance) :=
  { TBOp := fun x y => wrapZ 256 (x - y); TBOpInj := @zw_sub 8 _ _ 256 eq_refl }.
Add Zify BinOp Op_w8_sub.

#[global] Instance Op_w8_mul : BinOp (@word.mul 8 w8_word_instance) :=
  { TBOp := fun x y => wrapZ 256 (x * y); TBOpInj := @zw_mul 8 _ _ 256 eq_refl }.
Add Zify BinOp Op_w8_mul.

#[global] Instance Op_w8_opp : UnOp (@word.opp 8 w8_word_instance) :=
  { TUOp := fun x => wrapZ 256 (- x); TUOpInj := @zw_opp 8 _ _ 256 eq_refl }.
Add Zify UnOp Op_w8_opp.

#[global] Instance Op_w8_or : BinOp (@word.or 8 w8_word_instance) :=
  { TBOp := fun x y => wrapZ 256 (Z.lor x y); TBOpInj := @zw_or 8 _ _ 256 eq_refl }.
Add Zify BinOp Op_w8_or.

#[global] Instance Op_w8_and : BinOp (@word.and 8 w8_word_instance) :=
  { TBOp := fun x y => wrapZ 256 (Z.land x y); TBOpInj := @zw_and 8 _ _ 256 eq_refl }.
Add Zify BinOp Op_w8_and.

#[global] Instance Op_w8_xor : BinOp (@word.xor 8 w8_word_instance) :=
  { TBOp := fun x y => wrapZ 256 (Z.lxor x y); TBOpInj := @zw_xor 8 _ _ 256 eq_refl }.
Add Zify BinOp Op_w8_xor.

#[global] Instance Op_w8_not : UnOp (@word.not 8 w8_word_instance) :=
  { TUOp := fun x => wrapZ 256 (Z.lnot x); TUOpInj := @zw_not 8 _ _ 256 eq_refl }.
Add Zify UnOp Op_w8_not.

#[global] Instance Op_w8_ndn : BinOp (@word.ndn 8 w8_word_instance) :=
  { TBOp := fun x y => wrapZ 256 (Z.ldiff x y); TBOpInj := @zw_ndn 8 _ _ 256 eq_refl }.
Add Zify BinOp Op_w8_ndn.

#[global] Instance Rel_w8_eq : BinRel (@eq (@word.rep 8 w8_word_instance)) :=
  { TR := @eq Z; TRInj := zw_eq }.
Add Zify BinRel Rel_w8_eq.

(** ** 16-bit words. Not in a [Section]: [Add Zify] registrations do not
    survive [End Section]. *)

#[global] Instance Inj_w16 : InjTyp (@word.rep 16 w16_word_instance) Z :=
  mkinj _ _ uint.Z (fun z => 0 ≤ z < 65536) (@zw_range 16 _ _ 65536 eq_refl).
Add Zify InjTyp Inj_w16.

#[global] Instance Op_w16_unsigned : UnOp (@word.unsigned 16 w16_word_instance) :=
  { TUOp := fun z => z; TUOpInj := fun _ => eq_refl }.
Add Zify UnOp Op_w16_unsigned.

#[global] Instance Op_w16_signed : UnOp (@word.signed 16 w16_word_instance) :=
  { TUOp := fun z => wrapZ 65536 (z + 32768) - 32768; TUOpInj := @zw_signed 16 _ _ 65536 32768 eq_refl eq_refl }.
Add Zify UnOp Op_w16_signed.

#[global] Instance Op_w16_of_Z : UnOp (@word.of_Z 16 w16_word_instance) :=
  { TUOp := wrapZ 65536; TUOpInj := @zw_of_Z 16 _ _ 65536 eq_refl }.
Add Zify UnOp Op_w16_of_Z.

#[global] Instance Op_w16_add : BinOp (@word.add 16 w16_word_instance) :=
  { TBOp := fun x y => wrapZ 65536 (x + y); TBOpInj := @zw_add 16 _ _ 65536 eq_refl }.
Add Zify BinOp Op_w16_add.

#[global] Instance Op_w16_sub : BinOp (@word.sub 16 w16_word_instance) :=
  { TBOp := fun x y => wrapZ 65536 (x - y); TBOpInj := @zw_sub 16 _ _ 65536 eq_refl }.
Add Zify BinOp Op_w16_sub.

#[global] Instance Op_w16_mul : BinOp (@word.mul 16 w16_word_instance) :=
  { TBOp := fun x y => wrapZ 65536 (x * y); TBOpInj := @zw_mul 16 _ _ 65536 eq_refl }.
Add Zify BinOp Op_w16_mul.

#[global] Instance Op_w16_opp : UnOp (@word.opp 16 w16_word_instance) :=
  { TUOp := fun x => wrapZ 65536 (- x); TUOpInj := @zw_opp 16 _ _ 65536 eq_refl }.
Add Zify UnOp Op_w16_opp.

#[global] Instance Op_w16_or : BinOp (@word.or 16 w16_word_instance) :=
  { TBOp := fun x y => wrapZ 65536 (Z.lor x y); TBOpInj := @zw_or 16 _ _ 65536 eq_refl }.
Add Zify BinOp Op_w16_or.

#[global] Instance Op_w16_and : BinOp (@word.and 16 w16_word_instance) :=
  { TBOp := fun x y => wrapZ 65536 (Z.land x y); TBOpInj := @zw_and 16 _ _ 65536 eq_refl }.
Add Zify BinOp Op_w16_and.

#[global] Instance Op_w16_xor : BinOp (@word.xor 16 w16_word_instance) :=
  { TBOp := fun x y => wrapZ 65536 (Z.lxor x y); TBOpInj := @zw_xor 16 _ _ 65536 eq_refl }.
Add Zify BinOp Op_w16_xor.

#[global] Instance Op_w16_not : UnOp (@word.not 16 w16_word_instance) :=
  { TUOp := fun x => wrapZ 65536 (Z.lnot x); TUOpInj := @zw_not 16 _ _ 65536 eq_refl }.
Add Zify UnOp Op_w16_not.

#[global] Instance Op_w16_ndn : BinOp (@word.ndn 16 w16_word_instance) :=
  { TBOp := fun x y => wrapZ 65536 (Z.ldiff x y); TBOpInj := @zw_ndn 16 _ _ 65536 eq_refl }.
Add Zify BinOp Op_w16_ndn.

#[global] Instance Rel_w16_eq : BinRel (@eq (@word.rep 16 w16_word_instance)) :=
  { TR := @eq Z; TRInj := zw_eq }.
Add Zify BinRel Rel_w16_eq.

(** ** 32-bit words. Not in a [Section]: [Add Zify] registrations do not
    survive [End Section]. *)

#[global] Instance Inj_w32 : InjTyp (@word.rep 32 w32_word_instance) Z :=
  mkinj _ _ uint.Z (fun z => 0 ≤ z < 4294967296) (@zw_range 32 _ _ 4294967296 eq_refl).
Add Zify InjTyp Inj_w32.

#[global] Instance Op_w32_unsigned : UnOp (@word.unsigned 32 w32_word_instance) :=
  { TUOp := fun z => z; TUOpInj := fun _ => eq_refl }.
Add Zify UnOp Op_w32_unsigned.

#[global] Instance Op_w32_signed : UnOp (@word.signed 32 w32_word_instance) :=
  { TUOp := fun z => wrapZ 4294967296 (z + 2147483648) - 2147483648; TUOpInj := @zw_signed 32 _ _ 4294967296 2147483648 eq_refl eq_refl }.
Add Zify UnOp Op_w32_signed.

#[global] Instance Op_w32_of_Z : UnOp (@word.of_Z 32 w32_word_instance) :=
  { TUOp := wrapZ 4294967296; TUOpInj := @zw_of_Z 32 _ _ 4294967296 eq_refl }.
Add Zify UnOp Op_w32_of_Z.

#[global] Instance Op_w32_add : BinOp (@word.add 32 w32_word_instance) :=
  { TBOp := fun x y => wrapZ 4294967296 (x + y); TBOpInj := @zw_add 32 _ _ 4294967296 eq_refl }.
Add Zify BinOp Op_w32_add.

#[global] Instance Op_w32_sub : BinOp (@word.sub 32 w32_word_instance) :=
  { TBOp := fun x y => wrapZ 4294967296 (x - y); TBOpInj := @zw_sub 32 _ _ 4294967296 eq_refl }.
Add Zify BinOp Op_w32_sub.

#[global] Instance Op_w32_mul : BinOp (@word.mul 32 w32_word_instance) :=
  { TBOp := fun x y => wrapZ 4294967296 (x * y); TBOpInj := @zw_mul 32 _ _ 4294967296 eq_refl }.
Add Zify BinOp Op_w32_mul.

#[global] Instance Op_w32_opp : UnOp (@word.opp 32 w32_word_instance) :=
  { TUOp := fun x => wrapZ 4294967296 (- x); TUOpInj := @zw_opp 32 _ _ 4294967296 eq_refl }.
Add Zify UnOp Op_w32_opp.

#[global] Instance Op_w32_or : BinOp (@word.or 32 w32_word_instance) :=
  { TBOp := fun x y => wrapZ 4294967296 (Z.lor x y); TBOpInj := @zw_or 32 _ _ 4294967296 eq_refl }.
Add Zify BinOp Op_w32_or.

#[global] Instance Op_w32_and : BinOp (@word.and 32 w32_word_instance) :=
  { TBOp := fun x y => wrapZ 4294967296 (Z.land x y); TBOpInj := @zw_and 32 _ _ 4294967296 eq_refl }.
Add Zify BinOp Op_w32_and.

#[global] Instance Op_w32_xor : BinOp (@word.xor 32 w32_word_instance) :=
  { TBOp := fun x y => wrapZ 4294967296 (Z.lxor x y); TBOpInj := @zw_xor 32 _ _ 4294967296 eq_refl }.
Add Zify BinOp Op_w32_xor.

#[global] Instance Op_w32_not : UnOp (@word.not 32 w32_word_instance) :=
  { TUOp := fun x => wrapZ 4294967296 (Z.lnot x); TUOpInj := @zw_not 32 _ _ 4294967296 eq_refl }.
Add Zify UnOp Op_w32_not.

#[global] Instance Op_w32_ndn : BinOp (@word.ndn 32 w32_word_instance) :=
  { TBOp := fun x y => wrapZ 4294967296 (Z.ldiff x y); TBOpInj := @zw_ndn 32 _ _ 4294967296 eq_refl }.
Add Zify BinOp Op_w32_ndn.

#[global] Instance Rel_w32_eq : BinRel (@eq (@word.rep 32 w32_word_instance)) :=
  { TR := @eq Z; TRInj := zw_eq }.
Add Zify BinRel Rel_w32_eq.

(** ** 64-bit words. Not in a [Section]: [Add Zify] registrations do not
    survive [End Section]. *)

#[global] Instance Inj_w64 : InjTyp (@word.rep 64 w64_word_instance) Z :=
  mkinj _ _ uint.Z (fun z => 0 ≤ z < 18446744073709551616) (@zw_range 64 _ _ 18446744073709551616 eq_refl).
Add Zify InjTyp Inj_w64.

#[global] Instance Op_w64_unsigned : UnOp (@word.unsigned 64 w64_word_instance) :=
  { TUOp := fun z => z; TUOpInj := fun _ => eq_refl }.
Add Zify UnOp Op_w64_unsigned.

#[global] Instance Op_w64_signed : UnOp (@word.signed 64 w64_word_instance) :=
  { TUOp := fun z => wrapZ 18446744073709551616 (z + 9223372036854775808) - 9223372036854775808; TUOpInj := @zw_signed 64 _ _ 18446744073709551616 9223372036854775808 eq_refl eq_refl }.
Add Zify UnOp Op_w64_signed.

#[global] Instance Op_w64_of_Z : UnOp (@word.of_Z 64 w64_word_instance) :=
  { TUOp := wrapZ 18446744073709551616; TUOpInj := @zw_of_Z 64 _ _ 18446744073709551616 eq_refl }.
Add Zify UnOp Op_w64_of_Z.

#[global] Instance Op_w64_add : BinOp (@word.add 64 w64_word_instance) :=
  { TBOp := fun x y => wrapZ 18446744073709551616 (x + y); TBOpInj := @zw_add 64 _ _ 18446744073709551616 eq_refl }.
Add Zify BinOp Op_w64_add.

#[global] Instance Op_w64_sub : BinOp (@word.sub 64 w64_word_instance) :=
  { TBOp := fun x y => wrapZ 18446744073709551616 (x - y); TBOpInj := @zw_sub 64 _ _ 18446744073709551616 eq_refl }.
Add Zify BinOp Op_w64_sub.

#[global] Instance Op_w64_mul : BinOp (@word.mul 64 w64_word_instance) :=
  { TBOp := fun x y => wrapZ 18446744073709551616 (x * y); TBOpInj := @zw_mul 64 _ _ 18446744073709551616 eq_refl }.
Add Zify BinOp Op_w64_mul.

#[global] Instance Op_w64_opp : UnOp (@word.opp 64 w64_word_instance) :=
  { TUOp := fun x => wrapZ 18446744073709551616 (- x); TUOpInj := @zw_opp 64 _ _ 18446744073709551616 eq_refl }.
Add Zify UnOp Op_w64_opp.

#[global] Instance Op_w64_or : BinOp (@word.or 64 w64_word_instance) :=
  { TBOp := fun x y => wrapZ 18446744073709551616 (Z.lor x y); TBOpInj := @zw_or 64 _ _ 18446744073709551616 eq_refl }.
Add Zify BinOp Op_w64_or.

#[global] Instance Op_w64_and : BinOp (@word.and 64 w64_word_instance) :=
  { TBOp := fun x y => wrapZ 18446744073709551616 (Z.land x y); TBOpInj := @zw_and 64 _ _ 18446744073709551616 eq_refl }.
Add Zify BinOp Op_w64_and.

#[global] Instance Op_w64_xor : BinOp (@word.xor 64 w64_word_instance) :=
  { TBOp := fun x y => wrapZ 18446744073709551616 (Z.lxor x y); TBOpInj := @zw_xor 64 _ _ 18446744073709551616 eq_refl }.
Add Zify BinOp Op_w64_xor.

#[global] Instance Op_w64_not : UnOp (@word.not 64 w64_word_instance) :=
  { TUOp := fun x => wrapZ 18446744073709551616 (Z.lnot x); TUOpInj := @zw_not 64 _ _ 18446744073709551616 eq_refl }.
Add Zify UnOp Op_w64_not.

#[global] Instance Op_w64_ndn : BinOp (@word.ndn 64 w64_word_instance) :=
  { TBOp := fun x y => wrapZ 18446744073709551616 (Z.ldiff x y); TBOpInj := @zw_ndn 64 _ _ 18446744073709551616 eq_refl }.
Add Zify BinOp Op_w64_ndn.

#[global] Instance Rel_w64_eq : BinRel (@eq (@word.rep 64 w64_word_instance)) :=
  { TR := @eq Z; TRInj := zw_eq }.
Add Zify BinRel Rel_w64_eq.

(** A sanity check that the instances are picked up: [lia] alone can now do
    word arithmetic. The [word] tactic adds the unfolding of [W64]/[w64] and
    friends and the handling of the remaining operations. *)
Local Lemma zify_word_smoke (x y : @word.rep 64 w64_word_instance) :
  word.sub (word.add x y) y = x ∧ sint.Z (@word.of_Z 64 w64_word_instance (-1)) = -1.
Proof. split; lia. Qed.
