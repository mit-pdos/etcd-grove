/- Lean-first (no Rocq counterpart).

# The zero length word where the reader stopped (W3/W5 of `notes/wal-fsext-plan.md`, twenty-fifth session)

`ReadAll` in write mode reads to `io.EOF` (S/wal.go:578); the reader stops with `io.EOF` only at the
end of a file or at a zero length word (`decStep`'s `.stop .eof`, decoder.go:107-113), so the 8 bytes
from where it stopped are zero, the bytes past the file counting as zero (`getD … 0`). This is
`ZeroToEnd.specWalTail`'s zero-length-word premise at the tail's write position (`wal-tc16`'s proposed
form, over the tail's bytes `(bs.getD (wr + j) (0, [])).1 = 0`):

* `decStep_eof_zero`, `walDecodeFrom_eof_zero`, `walDecodeFiles_eof_zero`: at a `.eof` stop, the length
  word at the stop's offset in the last file is zero;
* `readAll_tailZeroWord`: over the segments read, the last one's bytes at `wr`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllFiles
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailCrashPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

theorem getD_take8_drop {bs : List w8} {off j : Nat} (hj : j < 8) :
    ((bs.drop off).take 8).getD j 0 = bs.getD (off + j) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj, List.getElem?_drop]

/-- **At a `.eof` stop of one step the length word is zero** (or the file has ended there). -/
theorem decStep_eof_zero (C : WalCodec) (last : Bool) {bs : List w8} {off : Nat} {c : w32}
    (h : decStep C last bs off c = .stop .eof) : ∀ j, j < 8 → bs.getD (off + j) 0 = 0 := by
  intro j hj
  unfold decStep at h
  dsimp only at h
  by_cases h0 : (bs.drop off).length = 0
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [List.length_drop] at h0; omega)]
    rfl
  rw [if_neg h0] at h
  by_cases h8 : (bs.drop off).length < 8
  · rw [if_pos h8] at h; cases h
  rw [if_neg h8] at h
  by_cases hl : leToU64 ((bs.drop off).take 8) = 0#64
  · have hlen : ((bs.drop off).take 8).length = 8 := by rw [List.length_take]; omega
    have he := leToU64_le _ hlen
    rw [hl, show (0#64 : w64) = W64 0 from rfl, u64Le_0] at he
    rw [← getD_take8_drop hj, ← he]; exact getD_rep8 hj
  · rw [if_neg hl] at h
    repeat' (first | (split at h) | (cases h))

/-- **At a `.eof` stop of a file's reader the length word at its offset is zero.** -/
theorem walDecodeFrom_eof_zero (C : WalCodec) (last : Bool) (bs : List w8) (off : Nat) (c : w32)
    (h : (walDecodeFrom C last bs off c).stop = .eof) :
    ∀ j, j < 8 → bs.getD ((walDecodeFrom C last bs off c).off + j) 0 = 0 := by
  induction off, c using walDecodeFrom.induct C last bs with
  | case1 off c s hs =>
    rw [walDecodeFrom_unfold, hs] at h ⊢
    simp only at h ⊢
    subst h
    exact decStep_eof_zero C last hs
  | case2 off c r len c' hs ih =>
    rw [walDecodeFrom_unfold, hs] at h ⊢
    exact ih h

/-- **At a `.eof` stop of the files' reader the length word at its offset in the last file is zero.** -/
theorem walDecodeFiles_eof_zero (C : WalCodec) :
    ∀ (fs : List (List w8)) (c : w32) (f : List w8), fs.getLast? = some f →
      (walDecodeFiles C fs c).stop = .eof →
      ∀ j, j < 8 → f.getD ((walDecodeFiles C fs c).off + j) 0 = 0
  | [], _, _, h, _ => by simp at h
  | [g], c, f, h, hs => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    exact walDecodeFrom_eof_zero C true g 0 c hs
  | g :: g' :: fs, c, f, h, hs => by
    simp only [walDecodeFiles] at hs ⊢
    by_cases h0 : (walDecodeFrom C false g 0 c).stop = .eof
    · rw [if_pos h0] at hs ⊢
      exact walDecodeFiles_eof_zero C (g' :: fs) _ f (by simpa using h) hs
    · rw [if_neg h0] at hs; exact absurd hs h0

/-- **`ReadAll`'s zero length word at the tail's write position** (see the file header): the reader of
the segments `gs` (the last `gl`) stopped at `io.EOF` at `wr`. -/
theorem readAll_tailZeroWord (C : WalCodec) {gs : List SegG} {gl : SegG} {c : w32} {wr : Nat}
    (hl : gs.getLast? = some gl) (hs : (walDecodeFiles C (gs.map segImg) c).stop = .eof)
    (ho : (walDecodeFiles C (gs.map segImg) c).off = wr) :
    ∀ j, j < 8 → (gl.bs.getD (wr + j) (0, [])).1 = 0 := by
  intro j hj
  have hl' : (gs.map segImg).getLast? = some (segImg gl) := by rw [List.getLast?_map, hl]; rfl
  have h := walDecodeFiles_eof_zero C _ c _ hl' hs j hj
  rw [ho] at h
  rw [← h]
  simp only [segImg, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases gl.bs[wr + j]? <;> rfl

end WalFs
end EtcdGrove
end Perennial

end
