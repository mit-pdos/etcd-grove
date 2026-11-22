/-
**`io.CopyFiles.spec`'s proof: the destination's shape and the pure steps** (session 9 of the WAL tester's
delegates, 2026-11-22; `notes/wal-units/tester.md`, the last handoff). The destination of the copy is held
whole, as `io.copyDst` says (`Spec/io/CopyFiles.lean`): its `OsMeta` `m` is `cpOk` (no mapping, no cut,
the crash low bound at most the size, the zeros known past the size), its bytes from 0 are its whole size.
Every write of the copy writes at the end (the destination starts empty, and both a `copy_file_range`
round and the fallback's `Write` write at its offset, which is its size until an error): `cpOk_pwPost`
(a `pwrite` at the end keeps `cpOk`, the size grows by what it wrote) and `pwBytes_end_vals` (the bytes
such a write leaves are the data's first `k`). Lean-first.
-/
module

public import Spec.io.CopyFiles
public import Proof.os.WriteChunks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- **The destination's `OsMeta` shape** (`io.copyDst`'s pure facts but the bytes'). -/
def io.cpOk (m : OsMeta) : Prop := m.maps = ∅ ∧ m.cut = none ∧ m.lo ≤ m.size ∧ m.ZfGe

/-- **A `pwrite` of `n > 0` bytes at the end of the file, of which it wrote `k`**, keeps `cpOk`, and
the size grows by `k`. -/
theorem io.cpOk_pwPost {m : OsMeta} (hm : io.cpOk m) {n k : Nat} (hn : 0 < n) (hk : k ≤ n) :
    io.cpOk (pwPost m m.size n k) ∧ (pwPost m m.size n k).size = m.size + k := by
  obtain ⟨hmaps, hcut, hlo, z, hz, hzs⟩ := hm
  have hsz : (pwPost m m.size n k).size = m.size + k := by
    show pwSize m.size m.size k = _
    unfold pwSize; split <;> omega
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hsz⟩
  · show (m.announce (min m.size m.size) (m.size + n) (max m.size (m.size + n))).maps = ∅
    rw [announce_maps]; exact hmaps
  · show (m.announce (min m.size m.size) (m.size + n) (max m.size (m.size + n))).cut = none
    simp only [OsMeta.announce, OsMeta.touch_cut]
    exact hcut
  · rw [hsz]
    show min m.lo (max m.size (m.size + n)) ≤ _
    omega
  · refine ⟨if min m.size m.size < m.size + n then max z (m.size + n) else z, ?_, ?_⟩
    · show (m.announce (min m.size m.size) (m.size + n) (max m.size (m.size + n))).zf = _
      rw [announce_zf, hz]; rfl
    · rw [hsz]; split <;> omega

/-- **The bytes a `pwrite` at the end leaves**: the data's first `k`. -/
theorem io.pwBytes_end_vals (sz : Nat) (data : List w8) (k nst : Nat) (zs : List Cands)
    (hk : k ≤ data.length) :
    (pwBytes sz sz data k nst [] zs).map Prod.fst = data.take k := by
  apply List.ext_getElem
  · rw [List.length_map, pwBytes_length, List.length_take]
    unfold pwSize; split <;> omega
  · intro j h1 h2
    simp only [pwBytes, List.getElem_map, List.getElem_range, pwByte, List.getElem_take]
    rw [List.length_take] at h2
    rw [if_pos (by omega), show sz + j - sz = j by omega]
    simp [List.getD, List.getElem?_eq_getElem (show j < data.length by omega)]

/-- The length of the bytes a `pwrite` at the end leaves. -/
theorem io.pwBytes_end_len (sz : Nat) (data : List w8) (k nst : Nat) (zs : List Cands)
    (hk : k ≤ data.length) : (pwBytes sz sz data k nst [] zs).length = k := by
  have := congrArg List.length (io.pwBytes_end_vals sz data k nst zs hk)
  rw [List.length_map, List.length_take] at this
  rw [this]; omega

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- Bytes held in two adjacent ranges. -/
theorem io.osBytes_append (i : Ino) (off : Nat) (dq : DFrac) (xs ys : List ByteG) :
    osBytes (GF := GF) i off dq (xs ++ ys) ⊣⊢
      osBytes i off dq xs ∗ osBytes i (off + xs.length) dq ys := by
  unfold osBytes
  exact bytesG_append _ i dq off xs ys

/-- **The destination, values `vs`**: `io.copyDst` at exactly `vs`, unfolded with `cpOk`. -/
theorem io.copyDst_intro (i : Ino) (P : List w8 → Prop) (m : OsMeta) (xs : List ByteG)
    (hm : io.cpOk m) (hl : xs.length = m.size) (hP : P (xs.map (·.1))) :
    osMeta (GF := GF) i (DFrac.own 1) m ∗ osBytes i 0 (DFrac.own 1) xs ⊢ io.copyDst i P := by
  iintro ⟨Hm, Hb⟩
  unfold io.copyDst
  iexists m, xs
  iframe Hm Hb
  obtain ⟨hmaps, hcut, hlo, hz⟩ := hm
  isplitl
  · rw [hmaps]
    unfold mcellsAny
    iapply BigSepM.bigSepM_empty.2
    itrivial
  · ipureintro
    exact ⟨hl, hmaps, hcut, hlo, hz, hP⟩

/-- **The destination opened** (`io.copyDst`'s parts, `cpOk`). -/
theorem io.copyDst_elim (i : Ino) (P : List w8 → Prop) :
    io.copyDst (GF := GF) i P ⊢ ∃ (m : OsMeta) (xs : List ByteG),
      osMeta i (DFrac.own 1) m ∗ osBytes i 0 (DFrac.own 1) xs ∗
      ⌜io.cpOk m ∧ xs.length = m.size ∧ P (xs.map (·.1))⌝ := by
  unfold io.copyDst
  iintro ⟨%m, %xs, Hm, Hb, -, %h⟩
  iexists m, xs
  iframe Hm Hb
  ipureintro
  obtain ⟨hl, hmaps, hcut, hlo, hz, hP⟩ := h
  exact ⟨⟨hmaps, hcut, hlo, hz⟩, hl, hP⟩

/-- `io.copyDst` is monotone in its property. -/
theorem io.copyDst_mono (i : Ino) (P Q : List w8 → Prop) (h : ∀ vs, P vs → Q vs) :
    io.copyDst (GF := GF) i P ⊢ io.copyDst i Q := by
  unfold io.copyDst
  iintro ⟨%m, %xs, Hm, Hb, Hc, %hh⟩
  iexists m, xs
  iframe Hm Hb Hc
  ipureintro
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hh
  exact ⟨h1, h2, h3, h4, h5, h _ h6⟩

/-- **The destination after a `pwrite` at its end** of `data` (non-empty), of which it wrote `k`. -/
theorem io.copyDst_after (i : Ino) (md : OsMeta) (xs : List ByteG) (data : List w8) (k nst : Nat)
    (zs : List Cands) (hok : io.cpOk md) (hxl : xs.length = md.size) (hn : 0 < data.length)
    (hk : k ≤ data.length) :
    osMeta (GF := GF) i (DFrac.own 1) (pwPost md md.size data.length k) ∗
      osBytes i 0 (DFrac.own 1) xs ∗
      osBytes i md.size (DFrac.own 1) (pwBytes md.size md.size data k nst [] zs) ⊢
      io.copyDst i (· = xs.map (·.1) ++ data.take k) := by
  iintro ⟨Hm, Hxs, Hn⟩
  have hp := io.cpOk_pwPost hok hn hk
  ihave Hb : osBytes (GF := GF) i 0 (DFrac.own 1) (xs ++ pwBytes md.size md.size data k nst [] zs) $$ [Hxs Hn]
  · iapply (io.osBytes_append i 0 _ xs _).2
    rw [Nat.zero_add, hxl]
    isplitl [Hxs]
    · iexact Hxs
    · iexact Hn
  iapply (io.copyDst_intro i _ _ (xs ++ pwBytes md.size md.size data k nst [] zs) hp.1
    (by rw [List.length_append, io.pwBytes_end_len _ _ _ _ _ hk, hp.2, hxl])
    (by rw [List.map_append, io.pwBytes_end_vals _ _ _ _ _ hk])) $$ [Hm Hb]
  iframe

end lemmas

end EtcdGrove
end Perennial
