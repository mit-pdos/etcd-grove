-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/CCCodecLen.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The part's own (raft without hand-written axioms, `notes/raft-noax-codec.md`).

# The conf change encodings' lengths

`MarshalConfChangeV1/V2`'s outputs are at most `ccLenMax` long (`PbContentOwn.lean`: every field
counted present), what their specs' posts bound the bytes by.
-/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.CCWireRoundtrip
public import KvRaft.Proof.go_etcd_io.raft.v3.PbContentOwn

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

/-! ## The encodings' lengths -/

theorem cc_varintSize_mono : ∀ (b a : Nat), a ≤ b → varintSize a ≤ varintSize b := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
  intro a hab
  unfold varintSize
  unfold varintEnc
  split
  · split <;> simp
  · rename_i ha
    split
    · omega
    · simp only [List.length_cons]
      have := ih (b / 128) (by omega) (a / 128) (Nat.div_le_div_right hab)
      unfold varintSize at this
      omega

theorem cc_lenSize_mono {a b : Nat} (h : a ≤ b) : lenSize a ≤ lenSize b := by
  unfold lenSize; have := cc_varintSize_mono b a h; omega

theorem ccEncOpt_varint_le (tag : w8) (o : Option w64) :
    (ccEncOpt tag ccVarint o).length ≤ fieldVarintSize (uint.nat (o.getD (W64 0))) := by
  cases o with
  | none => simp [ccEncOpt]
  | some v => simp [ccEncOpt, ccVarint, fieldVarintSize, varintSize]; omega

theorem ccEncOpt_enum_le [GooseExts] (tag : w8) (o : Option w32) :
    (ccEncOpt tag ccEnumEnc o).length ≤ fieldVarintSize (enumWire (o.getD (W32 0))) := by
  cases o with
  | none => simp [ccEncOpt]
  | some t =>
    simp only [ccEncOpt, ccEnumEnc, ccVarint, fieldVarintSize, enumWire, varintSize, List.length_cons,
      Option.getD_some]
    have : uint.nat (W64 (sint.Z t)) = (uint.Z (W64 (sint.Z t))).toNat := by word
    rw [this]; omega

theorem ccEncOpt_bytes_le (tag : w8) (o : Option (List w8))
    (h : ∀ c, o = some c → c.length < 2 ^ 64) :
    (ccEncOpt tag ccBytesEnc o).length ≤ lenSize (o.getD []).length := by
  cases o with
  | none => simp [ccEncOpt]
  | some x =>
    have hx := h x rfl
    simp only [ccEncOpt, ccBytesEnc, ccVarint, lenSize, varintSize, List.length_cons,
      List.length_append, Option.getD_some]
    have : uint.nat (W64 (x.length : Int)) = x.length := by word
    rw [this]; omega

/-- `MarshalConfChangeV1`'s output is at most `ccLenMax` long (every field counted present). -/
theorem ccEncodeV1_length_le [GooseExts] (id : Option w64) (ty : Option w32) (nid : Option w64)
    (ctx : Option (List w8)) (hctx : ∀ c, ctx = some c → c.length < 2 ^ 64) (uf : List w8) :
    (ccEncodeV1 id ty nid ctx ++ uf).length ≤
      ccLenMax (.v1 ⟨ty.getD (W32 0), nid.getD (W64 0), ctx.getD [], id.getD (W64 0)⟩ uf) := by
  unfold ccEncodeV1
  simp only [ccLenMax, List.length_append]
  have := ccEncOpt_varint_le (W8 8) id
  have := ccEncOpt_enum_le (W8 16) ty
  have := ccEncOpt_varint_le (W8 24) nid
  have := ccEncOpt_bytes_le (W8 34) ctx hctx
  omega

theorem ccEncodeSingle_length_le' [GooseExts] {c : ConfChangeSingleM} {e : List w8}
    (h : CCSingleEnc c e) :
    e.length ≤ fieldVarintSize (enumWire c.Type') + fieldVarintSize (uint.nat c.NodeId') := by
  obtain ⟨ty, nid, rfl, h1, h2⟩ := h
  unfold ccEncodeSingle
  rw [List.length_append, ← h1, ← h2]
  have := ccEncOpt_enum_le (W8 8) ty
  have := ccEncOpt_varint_le (W8 16) nid
  omega

theorem ccEncChanges_length_le [GooseExts] :
    ∀ (chs : List (ConfChangeSingleM × List w8)) (encs : List (List w8)),
    List.Forall₂ (fun ch e => CCSingleWireEnc ch.1 ch.2 e ∧ e.length < 2^64) chs encs →
    (ccEncChanges encs).length ≤
      (chs.map fun ch => lenSize (fieldVarintSize (enumWire ch.1.Type') +
        fieldVarintSize (uint.nat ch.1.NodeId') + ch.2.length)).sum := by
  intro chs encs H
  induction H with
  | nil => simp [ccEncChanges]
  | @cons ch e chs' encs' hce _ ih =>
    simp only [ccEncChanges, List.map_cons, List.sum_cons, List.length_append]
    obtain ⟨⟨known, hknown, heq, _⟩, h22⟩ := hce
    have hl := ccEncodeSingle_length_le' hknown
    have hlen : e.length = known.length + ch.2.length := by rw [heq, List.length_append]
    have he : (W8 18 :: ccBytesEnc e).length = lenSize e.length := by
      have : uint.nat (W64 (e.length : Int)) = e.length := by word
      simp only [List.length_cons, ccBytesEnc, ccVarint, List.length_append, lenSize, varintSize, this]
      omega
    have hm := cc_lenSize_mono (show e.length ≤ fieldVarintSize (enumWire ch.1.Type') +
      fieldVarintSize (uint.nat ch.1.NodeId') + ch.2.length by omega)
    omega

/-- `MarshalConfChangeV2`'s output is at most `ccLenMax` long. -/
theorem ccEncodeV2_length_le [GooseExts] (t : Option w32)
    (chs : List (ConfChangeSingleM × List w8)) (encs : List (List w8))
    (H : List.Forall₂ (fun ch e => CCSingleWireEnc ch.1 ch.2 e ∧ e.length < 2^64) chs encs)
    (ctx : Option (List w8)) (hctx : ∀ c, ctx = some c → c.length < 2 ^ 64) (uf : List w8) :
    (ccEncodeV2 t encs ctx ++ uf).length ≤ ccLenMax (.v2 (t.getD (W32 0)) chs (ctx.getD []) uf) := by
  unfold ccEncodeV2
  simp only [ccLenMax, List.length_append]
  have := ccEncOpt_enum_le (W8 8) t
  have := ccEncChanges_length_le chs encs H
  have := ccEncOpt_bytes_le (W8 26) ctx hctx
  omega

end EtcdGrove
end Perennial
