/- Lean-first (no Rocq counterpart).

# `cut`'s rename: the program's premises of `walCut_osAUnc` (W2, step 6; pure)

* `walNameP_walFileName`: a segment's name is a `.wal` name.
* `cutName_free`: the new name, above the directory's largest `.wal` name, is free.
* `recFrames_mod8`: the frames are 8-aligned; `recsFit_of_frames`: frames below `2^56` fit.
* `tailStream_len_split`: a quiescent, flushed handle's encoder offset is its stream's length.
* `cutHdrZeros`: the zeros after the headers, none or at least a frame header's 8.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutHdrStream

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

section pure
variable [GooseExts]

theorem walNameP_walFileName (sq ix : Nat) : walNameP (walFileName sq ix) = true := by
  unfold walNameP walFileName
  simp only [decide_eq_true_eq]
  exact List.suffix_append _ _

/-- **The new name is free**: the directory's `.wal` names are at most `nm0`, below it. -/
theorem cutName_free {cur : GMap GoString Node} {nm0 bt : GoString}
    (hl : ∀ b n, cur !! b = some n → walNameP b = true → b = nm0 ∨ go.GoStringLt b nm0)
    (hlt : go.GoStringLt nm0 bt) (hw : walNameP bt = true) : cur !! bt = none := by
  cases hc : cur !! bt with
  | none => rfl
  | some n =>
    rcases hl bt n hc hw with rfl | h
    · exact absurd hlt (go.goStringLt_irrefl _)
    · exact absurd h (go.goStringLt_asymm hlt)

theorem frame_mod8 (d : List w8) : (frame d).length % 8 = 0 := by
  rw [frame_length]; have := framePad_add_mod d.length; omega

theorem recFrames_mod8 (C : WalCodec) : ∀ rs : List WalRec, (recFrames C rs).length % 8 = 0
  | [] => rfl
  | r :: rs => by
    rw [recFrames_cons, List.length_append]
    have := frame_mod8 (C.encRec r); have := recFrames_mod8 C rs; omega

theorem recsFit_of_frames (C : WalCodec) : ∀ rs : List WalRec,
    (recFrames C rs).length < 2 ^ 56 → RecsFit C rs
  | [] => fun _ r hr => absurd hr (by simp)
  | r :: rs => fun h r' hr' => by
    rw [recFrames_cons, List.length_append, frame_length] at h
    rcases List.mem_cons.1 hr' with rfl | hr'
    · omega
    · exact recsFit_of_frames C rs (by omega) r' hr'

/-- A quiescent handle whose encoder holds nothing: its offset is its stream's end. -/
theorem tailStream_len_split (Mr : WalMarshal) (h : WalHS) (hs : WalHS.Split Mr h) (hr : h.rest = 0)
    (hp : h.pend = []) : (tailStream Mr h.H h.md h.cuts).length = h.o0 + h.out.length := by
  obtain ⟨h1, h2, -⟩ := hs
  unfold WalHS.encRecs at h1 h2
  rw [hr, Nat.sub_zero, List.take_length] at h1 h2
  rw [hp, List.append_nil] at h1
  rw [tailStream_recs]
  have := congrArg List.length h1
  rw [List.length_append, List.length_take] at this
  omega

/-- The zeros after the headers: none, or at least 8 bytes. -/
theorem cutHdrZeros (s L : Nat) (hs : s % 8 = 0) (hL : L % 8 = 0) :
    max s (0 + L) - L = 0 ∨ 8 ≤ max s (0 + L) - L := by
  omega

end pure

end WalFs
end EtcdGrove
end Perennial

end
