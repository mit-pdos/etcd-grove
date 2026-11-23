/-
Ported from dsverify-lab examples/paxos/proof/Paxos/Proof/Wire.lean (lab master 7a84fb35; notes/dsv-paxos.md).

The wire format (pure): a message's encoding (`marshalMessage`'s bytes), its frame (the length
of the encoding as an 8-byte little-endian word, then the encoding: `encodeFrame`), and a
stream of frames. `parse_frames_prefix` is what a reader needs: a stream that is a prefix of
frames of `ms`, read as whole frames, is frames of a prefix of `ms`.
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.Base

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.xiang90.paxos

section wire
variable [GooseExts]

/-- `marshalMessage m`'s bytes: five integers, then the value, length-prefixed. -/
def encMsg (m : message) : List w8 :=
  u64Le m.from' ++ u64Le m.to' ++ u64Le m.typ' ++ u64Le m.n' ++ u64Le m.prevn' ++
    u64Le (W64 m.value'.length) ++ m.value'

/-- `encodeFrame m`'s bytes. -/
def frame (m : message) : List w8 := u64Le (W64 (encMsg m).length) ++ encMsg m

/-- A stream of whole frames. -/
def frames (ms : List message) : List w8 := (ms.map frame).flatten

/-- Messages whose value fits the model's slices (`len < 2^48`, the input premise's bound). -/
def msgWf (m : message) : Prop := (m.value'.length : Int) < 2 ^ 48

theorem encMsg_length (m : message) : (encMsg m).length = 48 + m.value'.length := by
  simp [encMsg, u64Le_length]; omega

theorem frames_append (a b : List message) : frames (a ++ b) = frames a ++ frames b := by
  simp [frames]

theorem frames_cons (m : message) (ms : List message) :
    frames (m :: ms) = frame m ++ frames ms := by simp [frames]

theorem W64_len_inj (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : W64 (a : Int) = W64 (b : Int)) : a = b := by
  have h2 := congrArg BitVec.toNat h
  simp at h2
  omega

theorem uint_nat_W64_len (a : Nat) (ha : a < 2 ^ 64) : uint.nat (W64 (a : Int)) = a := by
  word

theorem encMsg_inj (a b : message) (h : encMsg a = encMsg b) : a = b := by
  have hl := congrArg List.length h
  simp only [encMsg_length] at hl
  unfold encMsg at h
  obtain ⟨h, hv⟩ := List.append_inj' h (by omega)
  obtain ⟨h, h6⟩ := List.append_inj' h (by simp [u64Le_length])
  obtain ⟨h, h5⟩ := List.append_inj' h (by simp [u64Le_length])
  obtain ⟨h, h4⟩ := List.append_inj' h (by simp [u64Le_length])
  obtain ⟨h, h3⟩ := List.append_inj' h (by simp [u64Le_length])
  obtain ⟨h1, h2⟩ := List.append_inj' h (by simp [u64Le_length])
  cases a; cases b
  simp only at *
  rw [u64Le_inj h1, u64Le_inj h2, u64Le_inj h3, u64Le_inj h4, u64Le_inj h5, hv]

theorem frame_prefix (a b : message) (x y : List w8) (ha : msgWf a) (hb : msgWf b)
    (h : frame a ++ x <+: frame b ++ y) : a = b ∧ x <+: y := by
  obtain ⟨t, ht⟩ := h
  unfold frame at ht
  simp only [List.append_assoc] at ht
  obtain ⟨hh, ht⟩ := List.append_inj ht (by simp [u64Le_length])
  have hlen : (encMsg a).length = (encMsg b).length := by
    unfold msgWf at ha hb
    apply W64_len_inj _ _ _ _ (u64Le_inj hh) <;> rw [encMsg_length] <;> omega
  obtain ⟨he, ht⟩ := List.append_inj ht hlen
  exact ⟨encMsg_inj _ _ he, ⟨t, by rw [ht]⟩⟩

/-- `parse_frames_prefix` with the messages read so far well formed (as they are for a reader:
each comes from a stream of messages that fit). Without it the statement is false: a message
`d` whose value is `2^64` bytes longer than `m`'s has the same header as `m`. -/
theorem parse_frames_prefix_wf (done ms : List message) (n : w64) (body : List w8)
    (hwf : ∀ m ∈ ms, msgWf m) (hdwf : ∀ m ∈ done, msgWf m) (hn : uint.nat n = body.length)
    (h : frames done ++ (u64Le n ++ body) <+: frames ms) :
    ∃ m, done ++ [m] <+: ms ∧ u64Le n ++ body = frame m := by
  induction done generalizing ms with
  | nil =>
    simp only [frames, List.map_nil, List.flatten_nil, List.nil_append] at h
    cases ms with
    | nil =>
      have := h.length_le
      simp [u64Le_length] at this
    | cons m ms' =>
      have hm := hwf m (by simp)
      obtain ⟨t, ht⟩ := h
      simp only [List.map_cons, List.flatten_cons, frame, List.append_assoc] at ht
      obtain ⟨hh, ht⟩ := List.append_inj ht (by simp [u64Le_length])
      have hn' := u64Le_inj hh
      have hbl : body.length = (encMsg m).length := by
        unfold msgWf at hm
        rw [← hn, hn', uint_nat_W64_len]
        rw [encMsg_length]; omega
      obtain ⟨hb, -⟩ := List.append_inj ht hbl
      refine ⟨m, by simp, ?_⟩
      rw [frame, hn', hb]
  | cons d done' ih =>
    cases ms with
    | nil =>
      have := h.length_le
      simp [frames, frame, u64Le_length] at this
    | cons m ms' =>
      rw [frames_cons, frames_cons, List.append_assoc] at h
      obtain ⟨rfl, h'⟩ := frame_prefix d m _ _ (hdwf d (by simp)) (hwf m (by simp)) h
      obtain ⟨m', hp, hf⟩ := ih ms' (fun x hx => hwf x (by simp [hx]))
        (fun x hx => hdwf x (by simp [hx])) h'
      exact ⟨m', by simpa using hp, hf⟩

/-- A reader's view: if `frames done ++ hdr ++ body` (with `hdr` the 8-byte length of `body`, of
messages that fit) is a prefix of `frames ms`, then `hdr ++ body` is the frame of the next
message of `ms`. -/
theorem parse_frames_prefix (done ms : List message) (n : w64) (body : List w8)
    (hwf : ∀ m ∈ ms, msgWf m) (hdwf : ∀ m ∈ done, msgWf m) (hn : uint.nat n = body.length)
    (h : frames done ++ (u64Le n ++ body) <+: frames ms) :
    ∃ m, done ++ [m] <+: ms ∧ u64Le n ++ body = frame m :=
  parse_frames_prefix_wf done ms n body hwf hdwf hn h

end wire

end github_com.xiang90.paxos

end Perennial
