/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/encode.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.encode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

theorem encode.wp_proof : encode.spec (GF := GF) (hG := hG) := by
  intro replica seq kind val Hval
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  wp_apply wp_slice_make3 (V := w8) (W64 17) (W64 17 + W64 (val.length : Int)) ⟨by decide, by word⟩
    as %b ⟨Hb, Hbcap, %Hbc⟩
  rw [show List.replicate 17 (zero_val w8) =
    List.replicate 8 (W8 0) ++ List.replicate 9 (W8 0) from rfl]
  wp_apply encoding.binary.wp_LittleEndian_PutUint64 b (List.replicate 8 (W8 0))
    (List.replicate 9 (W8 0)) replica rfl $$ [$Hb] as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hr := u64Le_length replica
  simp only [List.length_append, List.length_replicate, hr] at Hlen
  have Hbl : sint.Z b.len = 17 := by obtain ⟨h1, h2⟩ := Hlen; word
  rw [if_pos (by rw [Hbc]; word)]
  icases (ownSlice_split_all (W64 8) b _ _ ⟨by decide, by rw [Hbl]; decide⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
  rw [show (u64Le replica ++ List.replicate 9 (W8 0)).drop (sint.nat (W64 8)) =
      List.replicate 8 (W8 0) ++ [W8 0] by
    rw [show sint.nat (W64 8) = (u64Le replica).length by rw [hr]; rfl, List.drop_left]; rfl]
  wp_auto
  wp_apply encoding.binary.wp_LittleEndian_PutUint64 _ (List.replicate 8 (W8 0))
    [W8 0] seq rfl $$ [$Hb2] as Hb2
  rw [show (u64Le replica ++ List.replicate 9 (W8 0)).take (sint.nat (W64 8)) = u64Le replica by
    rw [show sint.nat (W64 8) = (u64Le replica).length by rw [hr]; rfl, List.take_left]]
  ihave Hb := ownSlice_combine (W64 8) b (DFrac.own 1) (u64Le replica) (u64Le seq ++ [W8 0])
    (W64 0) b.len ⟨by rw [hr]; rfl, by decide, by decide, by rw [Hbl]; decide⟩ $$ Hb1 Hb2
  ihave Hb := (ownSlice_trivial_slice b (DFrac.own 1) _).2 $$ Hb
  rw [if_pos (by rw [Hbl]; decide)]
  wp_apply wp_store_slice_index b (sint.Z (W64 16)) _ kind $$ [$Hb] as Hb
  · ipureintro
    simp [hr, u64Le_length]
    decide
  wp_apply wp_string_to_bytes val as %sl ⟨Hsl, Hslcap⟩
  wp_apply wp_slice_append b _ sl val (DFrac.own 1) $$ [$Hb $Hbcap $Hsl] as %b' ⟨Hb', Hb'cap, -⟩
  iapply HΦ
  iframe Hb'cap
  have Hset : (u64Le replica ++ (u64Le seq ++ [W8 0])).set 16 kind =
      u64Le replica ++ u64Le seq ++ [kind] := by
    have hs := u64Le_length seq
    rw [show (16 : Nat) = (u64Le replica).length + ((u64Le seq).length + 0) by
      rw [hr, hs]]
    rw [List.set_append_right _ _ (by omega)]
    simp
  rw [Hset]
  unfold encodeOp
  iexact Hb'

end proof

end register
end EtcdGrove
end Perennial
