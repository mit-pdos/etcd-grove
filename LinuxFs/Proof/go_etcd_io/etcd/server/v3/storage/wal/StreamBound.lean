/- Lean-first (no Rocq counterpart).

# The tail's stream bound (W6 of `notes/wal-fsext-plan.md`, thirteenth session; pure)

What bounds the tail's stream, so that the encoder's offset and pending bytes stay below ext4's maximum
offset (`0xffffffff000`, `walHandleIn`'s bound) across a `Save` (ledger 2026-11-14, "the batch's size"):

* a frame is at most its record's data plus 64 bytes (`frame_walRecEnc_tight`: the record's type, CRC
  and length fields are varints of at most 3, 6 and 10 bytes, the frame's length word 8, its padding 7);
* `walBatchBytes Mr es`: each entry's encoding plus 64, summed (`Save`'s premise, below `2 ^ 40`);
* `saveOp_frames_le`: a `Save`'s records' frames are at most its batch's bytes plus the state's;
* `walPend_le`: the page writer's pending bytes are at most its buffer (`2 ^ 18`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleAppend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Fs WalEnc

section pure
variable [GooseExts]

theorem wal_varintSize_le_of_lt : ∀ (k n : Nat), n < 2 ^ (7 * (k + 1)) → varintSize n ≤ k + 1 := by
  intro k
  induction k with
  | zero =>
    intro n h
    unfold varintSize
    rw [varintEnc, dite_eq_left_iff.2 (fun h' => absurd (by simpa using h) h')]
    simp
  | succ k ih =>
    intro n h
    unfold varintSize
    rw [varintEnc]
    split
    · simp
    · simp only [List.length_cons]
      have h2 : n / 128 < 2 ^ (7 * (k + 1)) := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        have : 2 ^ (7 * (k + 1 + 1)) = 2 ^ (7 * (k + 1)) * 128 := by
          rw [show 7 * (k + 1 + 1) = 7 * (k + 1) + 7 by omega, Nat.pow_add]
        omega
      have := ih (n / 128) h2
      unfold varintSize at this
      omega

theorem wal_varintSize_le_10 (n : Nat) (h : n < 2 ^ 63) : varintSize n ≤ 10 :=
  wal_varintSize_le_of_lt 9 n (by
    have : (2 : Nat) ^ 63 ≤ 2 ^ (7 * (9 + 1)) := Nat.pow_le_pow_right (by decide) (by decide)
    omega)

theorem wal_varintSize_le_5 (n : Nat) (h : n < 2 ^ 32) : varintSize n ≤ 5 :=
  wal_varintSize_le_of_lt 4 n (by
    have : (2 : Nat) ^ 32 ≤ 2 ^ (7 * (4 + 1)) := Nat.pow_le_pow_right (by decide) (by decide)
    omega)

theorem wal_varintSize_le_2 (n : Nat) (h : n < 2 ^ 8) : varintSize n ≤ 2 :=
  wal_varintSize_le_of_lt 1 n (by
    have : (2 : Nat) ^ 8 ≤ 2 ^ (7 * (1 + 1)) := Nat.pow_le_pow_right (by decide) (by decide)
    omega)

/-- A record of a small type, any CRC, and data `d`: at most `d` plus 20 bytes. -/
theorem recSize_tight (t : w64) (k : w32) (d : List w8) (ht : uint.nat t < 2 ^ 8)
    (hd : d.length < 2 ^ 63) : recSize (recOf ⟨t, k, d⟩) ≤ d.length + 20 := by
  have h1 := wal_varintSize_le_2 (uint.nat t) ht
  have h4 : uint.nat k < 2 ^ 32 := by unfold uint.nat; exact BitVec.isLt _
  have h2 := wal_varintSize_le_5 (uint.nat k) h4
  have h3 := wal_varintSize_le_10 d.length hd
  by_cases hc : t = crcType ∧ d = []
  · simp only [recSize, recOf, if_pos hc, List.length_nil]; omega
  · simp only [recSize, recOf, if_neg hc, List.length_nil]; omega

/-- **A frame is at most its record's data plus 64 bytes.** -/
theorem frame_walRecEnc_tight (t : w64) (k : w32) (d : List w8) (ht : uint.nat t < 2 ^ 8)
    (hd : d.length < 2 ^ 63) : (frame (walRecEnc ⟨t, k, d⟩)).length ≤ d.length + 64 := by
  have := recSize_tight t k d ht hd
  rw [frame_length, walRecEnc, recEnc_length]
  have h2 := framePad_lt (recSize (recOf ⟨t, k, d⟩))
  omega

/-- The frames of chained records of small types: at most each data plus 64, summed. -/
theorem recFrames_chainRecs_le (c : w32) (ds : List (w64 × List w8))
    (h : ∀ p ∈ ds, uint.nat p.1 < 2 ^ 8 ∧ p.2.length < 2 ^ 63) :
    (recFrames walCodec (chainRecs walCodec c ds)).length ≤ (ds.map (fun p => p.2.length + 64)).sum := by
  induction ds generalizing c with
  | nil => simp [chainRecs, recFrames_nil]
  | cons p ds ih =>
    obtain ⟨t, d⟩ := p
    have hp := h (t, d) (by simp)
    have := ih (walCodec.crc32c c d) (fun q hq => h q (by simp [hq]))
    have hf := frame_walRecEnc_tight t (walCodec.crc32c c d) d hp.1 hp.2
    simp only [chainRecs, recFrames_cons, List.length_append, List.map_cons, List.sum_cons]
    simp only [walCodec] at hf this ⊢
    omega

theorem walBatchBytes_entry (Mr : WalMarshal) (es : List EntryM) (e : EntryM) (he : e ∈ es) :
    (Mr.encEntry e).length + 64 ≤ walBatchBytes Mr es := by
  unfold walBatchBytes
  induction es with
  | nil => simp at he
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 he with rfl | hx
    · omega
    · have := ih hx; omega

/-- Each entry of a batch below `2 ^ 40` bytes is below `2 ^ 40` bytes (`saveOp_fit`'s premise). -/
theorem walBatchBytes_each (Mr : WalMarshal) (es : List EntryM) (h : walBatchBytes Mr es < 2 ^ 40) :
    ∀ e ∈ es, (Mr.encEntry e).length < 2 ^ 40 := fun e he => by
  have := walBatchBytes_entry Mr es e he; omega

/-- **A `Save`'s records' frames**: at most its batch's bytes plus its state's encoding and 64. -/
theorem saveOp_frames_le (Mr : WalMarshal) (hs : HardStateM) (es : List EntryM)
    (hS : (Mr.encState hs).length < 2 ^ 32) (hE : walBatchBytes Mr es < 2 ^ 40) (c : w32) :
    (recFrames walCodec (chainRecs walCodec c (opDs Mr (WalOpG.save hs es).toRaw.toM))).length ≤
      walBatchBytes Mr es + (Mr.encState hs).length + 64 := by
  have hE' := walBatchBytes_each Mr es hE
  rw [WalOpG.toM_toRaw]
  refine Nat.le_trans (recFrames_chainRecs_le c _ ?_) ?_
  · intro p hp
    simp only [opDs, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨e, he, rfl⟩ | hp
    · exact ⟨by show uint.nat entryType < 2 ^ 8; decide, by have := hE' e he; simp only; omega⟩
    · split at hp
      · simp at hp
      · simp only [List.mem_singleton] at hp
        subst hp
        exact ⟨by show uint.nat stateType < 2 ^ 8; decide, by show (Mr.encState hs).length < 2 ^ 63; omega⟩
  · simp only [opDs, List.map_append, List.map_map, List.sum_append]
    have e1 : ((es.map (fun e => (entryType, Mr.encEntry e))).map (fun p => p.2.length + 64)).sum =
        walBatchBytes Mr es := by
      unfold walBatchBytes; rw [List.map_map]; rfl
    rw [List.map_map] at e1
    rw [e1]
    split <;> simp <;> omega

/-- **The handle's stream end is its encoded records' frames** (`WalHS.Split`). -/
theorem WalHS.split_end {Mr : WalMarshal} {h : WalHS} (hs : h.Split Mr) :
    h.o0 + h.out.length + h.pend.length = (recFrames walCodec (h.encRecs Mr)).length := by
  obtain ⟨h1, h2, -⟩ := hs
  have := congrArg List.length h1
  simp only [List.length_append, List.length_take] at this
  omega

/-- The encoded records' frames are at most the tail's stream. -/
theorem WalHS.encFrames_le (Mr : WalMarshal) (h : WalHS) :
    (recFrames walCodec (h.encRecs Mr)).length ≤ (tailStream Mr h.H h.md h.cuts).length := by
  rw [tailStream_recs]
  unfold WalHS.encRecs
  have hp : recFrames walCodec ((tailRecs Mr h.H h.md h.cuts).take
      ((tailRecs Mr h.H h.md h.cuts).length - h.rest)) <+: recFrames walCodec (tailRecs Mr h.H h.md h.cuts) := by
    conv => rhs; rw [← List.take_append_drop ((tailRecs Mr h.H h.md h.cuts).length - h.rest)
      (tailRecs Mr h.H h.md h.cuts)]
    rw [recFrames_append]
    exact List.prefix_append _ _
  exact hp.length_le

/-- The stream end of a handle at most its tail's stream. -/
theorem WalHS.end_le {Mr : WalMarshal} {h : WalHS} (hs : h.Split Mr) :
    h.o0 + h.out.length + h.pend.length ≤ (tailStream Mr h.H h.md h.cuts).length := by
  rw [WalHS.split_end hs]; exact WalHS.encFrames_le Mr h

/-- A quiescent handle's stream end is its tail's stream. -/
theorem WalHS.end_rest0 {Mr : WalMarshal} {h : WalHS} (hs : h.Split Mr) (hr : h.rest = 0) :
    h.o0 + h.out.length + h.pend.length = (tailStream Mr h.H h.md h.cuts).length := by
  rw [WalHS.split_end hs, tailStream_recs]
  unfold WalHS.encRecs; rw [hr, Nat.sub_zero, List.take_length]

/-- **A cut's new tail stream** (its headers): below `2 ^ 43`, the metadata below `2 ^ 41` and the state's
encoding below `2 ^ 32`. -/
theorem cutStream_lt (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (hs : cuts.Pairwise (· ≤ ·)) (hle : ∀ b ∈ cuts, b ≤ H.length) (hmd : md.length < 2 ^ 41)
    (hS : (Mr.encState (walLastHS (H.map WalOpG.toM))).length < 2 ^ 32) :
    (tailStream Mr H md (cuts ++ [H.length])).length < 2 ^ 43 := by
  rw [tailStream_recs, tailRecs_cut Mr H md cuts hs hle, cutHdrRecs_frames]
  have h1 := frame_walRecEnc_tight crcType (hash.crc32.crc32c (tailCrc Mr H md cuts) []) []
    (by decide) (by simp)
  have h2 := frame_walRecEnc_tight metadataType
    (hash.crc32.crc32c (hash.crc32.crc32c (tailCrc Mr H md cuts) []) md) md (by decide) (by omega)
  have h3 := frame_walRecEnc_tight stateType (hash.crc32.crc32c (hash.crc32.crc32c
    (hash.crc32.crc32c (tailCrc Mr H md cuts) []) md) (Mr.encState (walLastHS (H.map WalOpG.toM))))
    (Mr.encState (walLastHS (H.map WalOpG.toM))) (by decide) (by omega)
  simp only [List.length_nil] at h1
  split <;> simp only [List.length_append, List.length_nil] <;> omega

/-- **A `Save`'s new tail stream**: the old one plus the batch's frames, below ext4's maximum offset when the
old one is below `2 ^ 43`. -/
theorem saveStream_le (Mr : WalMarshal) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat)
    (hs : HardStateM) (es : List EntryM) (hc : ∀ b ∈ cuts, b ≤ H.length)
    (hS : (Mr.encState hs).length < 2 ^ 32) (hE : walBatchBytes Mr es < 2 ^ 40)
    (h0 : (tailStream Mr H md cuts).length < 2 ^ 43) :
    (tailStream Mr (H ++ [(WalOpG.save hs es).toRaw]) md cuts).length ≤ 0xffffffff000 := by
  rw [tailStream_snoc Mr H md cuts _ hc, List.length_append]
  have := saveOp_frames_le Mr hs es hS hE (chainEnd walCodec 0#32 (allRecs Mr H md cuts))
  omega

end pure

end WalFs
end EtcdGrove
end Perennial

end
