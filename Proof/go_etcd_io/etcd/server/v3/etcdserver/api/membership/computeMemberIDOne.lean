/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/computeMemberID.lean`: the URL strings
(`StringSlice`, one URL), `sort.Strings` (one string), `strings.Join` (the string), the token appended,
`sha1.Sum`, `binary.BigEndian.Uint64` of its first 8 bytes. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.computeMemberIDOne
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.URLs__StringSlicePlain
public import Spec.encoding.binary.bigEndian__Uint64
public import Perennial.Spec.sort.Strings
public import Perennial.Spec.strings.Join
public import Perennial.Spec.crypto.sha1.Sum

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

theorem combine_append_single (xs : List w8) (b : w8) :
    LittleEndian.combine (xs ++ [b]) = LittleEndian.combine xs + 256 ^ xs.length * b.toNat := by
  induction xs with
  | nil => simp [LittleEndian.combine]
  | cons x xs ih =>
    simp only [List.cons_append, LittleEndian.combine, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 256 (256 ^ xs.length)]
    generalize 256 ^ xs.length = P
    omega

theorem foldl_be (l : List w8) (a : Nat) :
    l.foldl (fun acc b => acc * 256 + b.toNat) a = a * 256 ^ l.length + LittleEndian.combine l.reverse := by
  induction l generalizing a with
  | nil => simp [LittleEndian.combine]
  | cons b l ih =>
    rw [List.foldl_cons, ih, List.reverse_cons, combine_append_single, List.length_reverse,
      List.length_cons, Nat.pow_succ]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ l.length),
      Nat.mul_comm (BitVec.toNat b) (256 ^ l.length)]
    generalize 256 ^ l.length = P
    omega

theorem foldl_int_cast (l : List w8) (a : Nat) :
    l.foldl (fun (acc : Int) b => acc * 256 + (b.toNat : Int)) (a : Int) =
      ((l.foldl (fun acc b => acc * 256 + b.toNat) a : Nat) : Int) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldl_cons, List.foldl_cons, ← ih]
    congr 1

/-- `binary.BigEndian.Uint64`'s value of bytes is their big-endian value, `memberIdOf`'s fold. -/
theorem beToU64_eq_fold (bs : List w8) :
    beToU64 bs = W64 (bs.foldl (fun acc b => acc * 256 + b.toNat) 0) := by
  unfold beToU64
  rw [leToU64_unseal]
  unfold leToU64Def
  rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, foldl_int_cast, foldl_be]
  simp [W64]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

theorem membership.computeMemberID.wp_proofOne
    [go_etcd_io.etcd.client.pkg.v3.types.Assumptions] [_root_.Perennial.sort.Assumptions]
    [_root_.Perennial.strings.Assumptions] [_root_.Perennial.crypto.sha1.Assumptions]
    [encoding.binary.Assumptions]
    (hSS : types.URLs.StringSlicePlain.spec (GF := GF) (hG := hG))
    (hSort : _root_.Perennial.sort.Strings.spec (GF := GF) (hG := hG))
    (hJoin : _root_.Perennial.strings.Join.spec (GF := GF) (hG := hG))
    (hSum : _root_.Perennial.crypto.sha1.Sum.spec (GF := GF) (hG := hG))
    (hU64 : binary.bigEndian.Uint64.spec (GF := GF) (hG := hG)) :
    membership.computeMemberID.specOne (GF := GF) (hG := hG) := by
  intro sl u token hfips
  wp_start as #Hsl
  wp_auto
  wp_apply (hSS peerURLs_ptr (DFrac.own 1) sl [u]) $$ [peerURLs] as %out %ss ⟨peerURLs, Hout, %Hss⟩
  · iframe; iframe #
  wp_apply (hSort out ss) $$ [Hout] as %ss' ⟨Hout, %Hperm, %Hsorted⟩
  · iframe; ipureintro; simp [Hss.1]
  wp_apply (hJoin out ss' (DFrac.own 1) []) $$ [Hout] as Hout
  · iframe
  wp_apply wp_string_to_bytes ([].intercalate ss') as %b1 ⟨Hb1, Hb1cap⟩
  wp_apply wp_string_to_bytes token as %b2 ⟨Hb2, -⟩
  wp_apply (wp_slice_append b1 _ b2 _ (DFrac.own 1)) $$ [Hb1 Hb1cap Hb2] as %b3 ⟨Hb3, -, -⟩
  · iframe
  wp_auto
  wp_apply (hSum b3 (DFrac.own 1) _ hfips) $$ [Hb3] as Hb3
  · iframe
  generalize hH : crypto.sha1.sha1 ([].intercalate ss' ++ token) = H
  ihave %Hn := array_len _ _ _ _ $$ hash
  ihave Hs := slice_array (GF := GF) hash_ptr _ (array.mk 20 H) (by simp only; omega) $$ hash
  ihave ⟨-, Hs8, -⟩ := (ownSlice_slice (V := w8) (W64 0) (W64 8) _ (DFrac.own 1) H
    ⟨by decide, by decide, by word⟩).1 $$ Hs
  have hl8 : (subslice (sint.nat (W64 0)) (sint.nat (W64 8)) H).length = 8 := by
    simp only [subslice, List.length_drop, List.length_take]; word
  wp_apply (hU64 _ (subslice (sint.nat (W64 0)) (sint.nat (W64 8)) H) [] (DFrac.own 1) hl8) $$ [Hs8] as -
  · rw [List.append_nil]; iframe
  iapply HΦ
  ipureintro
  intro hp
  obtain ⟨hl, hget⟩ := Hss
  have h0 := hget 0 u rfl hp
  have hss : ss = [go!"http://" ++ u.Host'] := by
    match ss, hl, h0 with
    | [x], _, h0 => simp at h0; simp [h0]
  rw [hss] at Hperm
  have hss' : ss' = [go!"http://" ++ u.Host'] := List.perm_singleton.1 Hperm.symm
  subst hss'
  rw [beToU64_eq_fold]
  unfold membership.memberIdOf
  rw [← hH]
  simp [subslice, List.intercalate]

end proof

end EtcdGrove
end Perennial
