/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/encode.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.encode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

/-- `encode`'s spec, for a key and a value whose lengths sum to less than `2^62`: then the
capacity `17 + len(key) + len(val)` does not overflow an `int`. (Until 2026-10-19 `encode.spec`
bounded each by `2^62` only, which lets the sum overflow, making `make` panic in the model:
unprovable; it bounds each by `2^61` now.) -/
theorem encode.wp_proof_sum : ∀ (id : w64) (kind : w8) (key val : List w8),
    (key.length : Int) + (val.length : Int) < 2 ^ 62 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf }}
      (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.encode))
        (Val #id)) (Val #kind)) (Val #key)) (Val #val))
    {{ (b : GoSlice), RET #b; b ↦* encodeOp id kind key val ∗
        ownSliceCap w8 b (DFrac.own 1) }} := by
  intro id kind key val Hkv
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl'
  have e : W64 17 + W64 (key.length : Int) + W64 (val.length : Int) =
      W64 (17 + (key.length : Int) + (val.length : Int)) := by
    simp only [BitVec.ofInt_add]
  have Hcz : sint.Z (W64 (17 + (key.length : Int) + (val.length : Int))) =
      17 + key.length + val.length := by
    simp only [BitVec.toInt_ofInt]; rw [Int.bmod_eq_of_le] <;> omega
  have Hcap : 0 ≤ sint.Z (W64 17) ∧ sint.Z (W64 17) ≤
      sint.Z (W64 17 + W64 (key.length : Int) + W64 (val.length : Int)) := by
    constructor
    · decide
    · rw [e, Hcz, show sint.Z (W64 17) = 17 from rfl]; omega
  wp_apply wp_slice_make3 (V := w8) (W64 17) (W64 17 + W64 (key.length : Int) + W64 (val.length : Int))
    Hcap as %b ⟨Hb, Hbcap, %Hbc⟩
  rw [show List.replicate 17 (zero_val w8) =
    List.replicate 8 (W8 0) ++ List.replicate 9 (W8 0) from rfl]
  wp_apply encoding.binary.wp_LittleEndian_PutUint64 b (List.replicate 8 (W8 0))
    (List.replicate 9 (W8 0)) id rfl $$ [$Hb] as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hr := u64Le_length id
  simp only [List.length_append, List.length_replicate, hr] at Hlen
  have Hbl : sint.Z b.len = 17 := by obtain ⟨h1, h2⟩ := Hlen; word
  have Hbcz : sint.Z b.cap = 17 + key.length + val.length := by rw [Hbc, e, Hcz]
  rw [ite_eq_left (by rw [Hbl]; decide)]
  wp_apply wp_store_slice_index b (sint.Z (W64 8)) _ kind $$ [$Hb] as Hb
  · ipureintro
    simp [hr, u64Le_length]
    decide
  have Hset : (u64Le id ++ List.replicate 9 (W8 0)).set 8 kind =
      (u64Le id ++ [kind]) ++ List.replicate 8 (W8 0) := by
    rw [show (8 : Nat) = (u64Le id).length + 0 by rw [hr]]
    rw [List.set_append_right _ _ (by omega)]
    simp only [Nat.sub_self, List.append_assoc, List.singleton_append]
    rfl
  rw [Hset]
  have hA : (u64Le id ++ [kind]).length = 9 := by simp [hr]
  rw [ite_eq_left (by rw [Hbl, Hbcz]; refine ⟨by decide, by decide, by omega⟩)]
  icases (ownSlice_split_all (W64 9) b _ _ ⟨by decide, by rw [Hbl]; decide⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
  rw [show ((u64Le id ++ [kind]) ++ List.replicate 8 (W8 0)).drop
      (sint.nat (W64 9)) = List.replicate 8 (W8 0) ++ [] by
    rw [show sint.nat (W64 9) = 9 from rfl, List.drop_left' hA]; rfl]
  rw [show ((u64Le id ++ [kind]) ++ List.replicate 8 (W8 0)).take
      (sint.nat (W64 9)) = u64Le id ++ [kind] by
    rw [show sint.nat (W64 9) = 9 from rfl, List.take_left' hA]]
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_apply encoding.binary.wp_LittleEndian_PutUint64 _ (List.replicate 8 (W8 0))
    [] _ rfl $$ [$Hb2] as Hb2
  ihave Hb := ownSlice_combine (W64 9) b (DFrac.own 1) (u64Le id ++ [kind])
    _ (W64 0) b.len ⟨by rw [hA]; rfl, by decide, by decide, by rw [Hbl]; decide⟩ $$ Hb1 Hb2
  ihave Hb := (ownSlice_trivial_slice b (DFrac.own 1) _).2 $$ Hb
  wp_apply wp_string_to_bytes key as %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append b _ sl key (DFrac.own 1) $$ [$Hb $Hbcap $Hsl] as %b' ⟨Hb', Hb'cap, -⟩
  wp_apply wp_string_to_bytes val as %sl2 ⟨Hsl2, -⟩
  wp_apply wp_slice_append b' _ sl2 val (DFrac.own 1) $$ [$Hb' $Hb'cap $Hsl2] as %b'' ⟨Hb'', Hb''cap, -⟩
  iapply HΦ
  iframe Hb''cap
  unfold encodeOp
  simp only [List.append_nil]
  iexact Hb''

/-- `encode.spec` from `encode.wp_proof_sum`: each length below `2^61` bounds their sum. -/
theorem encode.wp_proof : encode.spec (GF := GF) (hG := hG) := by
  intro id kind key val Hk Hv
  exact encode.wp_proof_sum id kind key val (by omega)

end proof

end kvreconf
end EtcdGrove
end Perennial
