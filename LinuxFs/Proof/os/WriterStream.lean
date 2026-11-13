/-
**An `*os.File` is an `io.Writer` stream** (`io.writerStream`, `Proof/io/WriterStream.lean`): the
bridge from `(*os.File).Write` (`os.File.Write.wp_long`/`wp_empty`, `OffLong.lean`) to the stream
writer `ioutil.PageWriter` and the WAL's encoder write through. WAL W6 (2026-11-13, `wal-bridge`).

The file of inode `d.ino`, open at `fd` (writable), is written from the offset `o0`, where its
`OsMeta` was `m0` and its bytes from `o0` to its end `xs0` (whole: `osMeta … 1`, `osBytes … 1`;
not mapped, `m0.maps = ∅`). The stream's state after accepting `out` (`os.fileW`):

* the handle (`ownFile`, `osFd`) and the offset past `out` (`ownOff f (o0 + len out)`);
* the file's `OsMeta` `m` and its bytes `ys` from `o0` to its end, whole, with `os.StreamOk`:
  `m` is `m0` after one full write per accepted `Write` (`os.MetaChain`: the writes' chunking is
  the client's, and the `OsMeta` keeps it: each write moves the crash bounds by its own range);
  the bytes below `len out` hold `out`'s, each with its old candidates (below the old end) then one
  or more holding its value (each attempt of its write announced it); the bytes past it are
  `xs0`'s.

After a failed `Write` of `xs` (`os.fileB`): the state before it, the offset unknown, and the
file as the failed write left it (`os.File.Write.wp_long`'s error post: `pwPost`/`PwOutA`; for an
empty `xs`, unchanged). The stream accepts at most `lim` bytes, `o0 + lim < 2^62` (the model's
bound).

**Not crash-aware**: the bridge takes the file's resources whole, as `WriteAt`'s plain spec does.
A WAL segment's halves are in the WAL invariant (`segRes`, `wal/Inv.lean`), whose writes need a
crash-aware `Write` (as `File.WriteAt.specCrash`, `Spec/os/Crash.lean`); that bridge has the same
shape with `cfOwn`-like resources in place of `osMeta`/`osBytes`. Lean-first.
-/
module

public import LinuxFs.Proof.os.OffLong
public import Proof.io.WriterStream

@[expose] public section

noncomputable section

namespace Perennial

namespace os

open Fs

/-- `m` is `m0` after full writes at `o0` of `a` bytes in all, one after the other, each of
`k > 0` bytes at the end of the last (`pwPost` of a write that wrote all it announced). -/
inductive MetaChain (o0 : Nat) (m0 : OsMeta) : Nat → OsMeta → Prop
  | nil : MetaChain o0 m0 0 m0
  | step {a k : Nat} {m : OsMeta} : MetaChain o0 m0 a m → 0 < k →
      MetaChain o0 m0 (a + k) (pwPost m (o0 + a) k k)

/-- The file's state after a stream of writes of `out` at `o0` (the file header). -/
def StreamOk (m0 : OsMeta) (o0 : Nat) (xs0 : List ByteG) (out : List w8) (m : OsMeta)
    (ys : List ByteG) : Prop :=
  xs0.length = m0.size - o0 ∧
  MetaChain o0 m0 out.length m ∧ m.lo ≤ m.size ∧ m.maps = m0.maps ∧ m0.size ≤ m.size ∧
  o0 + out.length ≤ m.size ∧ ys.length = m.size - o0 ∧
  (∀ i, i < out.length → (ys.getD i (0, [])).1 = out.getD i 0 ∧
    ∃ c0 extra, (ys.getD i (0, [])).2 = c0 ++ extra ∧ extra ≠ [] ∧
      (∀ q ∈ extra, q.1 = out.getD i 0) ∧ (i < xs0.length → c0 = (xs0.getD i (0, [])).2)) ∧
  (∀ i, out.length ≤ i → ys.getD i (0, []) = xs0.getD i (0, []))

theorem StreamOk.start {m0 : OsMeta} {o0 : Nat} {xs0 : List ByteG} (hlo : m0.lo ≤ m0.size)
    (ho : o0 ≤ m0.size) (hxs : xs0.length = m0.size - o0) : StreamOk m0 o0 xs0 [] m0 xs0 :=
  ⟨hxs, .nil, hlo, rfl, Nat.le_refl _, by simpa using ho, hxs, fun i hi => absurd hi (by simp),
    fun _ _ => rfl⟩

theorem pwPost_size' (m : OsMeta) (off n k : Nat) : (pwPost m off n k).size = pwSize m.size off k := rfl
theorem pwPost_lo' (m : OsMeta) (off n k : Nat) :
    (pwPost m off n k).lo = min m.lo (max m.size (off + n)) := by simp [pwPost]
theorem pwPost_maps' (m : OsMeta) (off n k : Nat) : (pwPost m off n k).maps = m.maps := by
  simp [pwPost]

theorem getD_eq_getElem {α} (l : List α) (d : α) (i : Nat) (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- A full write of `xs` at the end of the stream. -/
theorem StreamOk.step {m0 : OsMeta} {o0 : Nat} {xs0 : List ByteG} {out xs : List w8} {m : OsMeta}
    {ys ys2 : List ByteG} (h : StreamOk m0 o0 xs0 out m ys) (hn : 0 < xs.length)
    (hp : PwOut m (o0 + out.length) xs xs.length ((ys.drop out.length).take xs.length) ys2) :
    StreamOk m0 o0 xs0 (out ++ xs) (pwPost m (o0 + out.length) xs.length xs.length)
      (ys.take out.length ++ ys2 ++ (ys.drop out.length).drop xs.length) := by
  obtain ⟨hx0, hch, hlo, hmaps, hsz0, hosz, hyl, hin, hpast⟩ := h
  obtain ⟨hl2, hb2⟩ := hp
  have hS : pwSize m.size (o0 + out.length) xs.length = max m.size (o0 + out.length + xs.length) := by
    unfold pwSize; rw [if_neg (by omega)]
  rw [hS] at hl2
  have hl2' : ys2.length = xs.length := by rw [hl2]; omega
  have hout : out.length ≤ ys.length := by omega
  have hxs0 : xs0.length ≤ ys.length := by omega
  have hT : (ys.take out.length).length = out.length := by rw [List.length_take]; omega
  have hxw : ((ys.drop out.length).take xs.length).length = min xs.length (ys.length - out.length) := by
    simp only [List.length_take, List.length_drop]
  -- the bytes, by position
  have gT : ∀ i, i < out.length →
      (ys.take out.length ++ ys2 ++ (ys.drop out.length).drop xs.length).getD i (0, []) =
        ys.getD i (0, []) := by
    intro i hi
    rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      List.getElem?_take_of_lt hi, ← List.getD_eq_getElem?_getD]
  have g2 : ∀ i (hi : out.length ≤ i) (hi2 : i < out.length + xs.length),
      (ys.take out.length ++ ys2 ++ (ys.drop out.length).drop xs.length).getD i (0, []) =
        ys2[i - out.length]'(by omega) := by
    intro i hi hi2
    rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hT,
      List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega), Option.getD_some]
  have gR : ∀ i, out.length + xs.length ≤ i →
      (ys.take out.length ++ ys2 ++ (ys.drop out.length).drop xs.length).getD i (0, []) =
        ys.getD i (0, []) := by
    intro i hi
    rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hT,
      List.getElem?_append_right (by omega), hl2', List.getElem?_drop, List.getElem?_drop,
      ← List.getD_eq_getElem?_getD]
    congr 1; omega
  refine ⟨hx0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_append]; exact .step hch hn
  · rw [pwPost_lo', pwPost_size', hS]; omega
  · rw [pwPost_maps']; exact hmaps
  · rw [pwPost_size', hS]; omega
  · rw [pwPost_size', hS, List.length_append]; omega
  · rw [pwPost_size', hS]; simp only [List.length_append, hT, hl2', List.length_drop]; omega
  · intro i hi
    rw [List.length_append] at hi
    by_cases hiL : i < out.length
    · rw [gT i hiL, show (out ++ xs).getD i 0 = out.getD i 0 by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hiL, ← List.getD_eq_getElem?_getD]]
      exact hin i hiL
    · have hiL' : out.length ≤ i := by omega
      rw [g2 i hiL' hi]
      have hgx : (out ++ xs).getD i 0 = xs.getD (i - out.length) 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hiL', ← List.getD_eq_getElem?_getD]
      rw [hgx]
      obtain ⟨hv, c0, extra, hc, hne, hq, hc0⟩ := hb2 (i - out.length) (by omega)
      refine ⟨?_, c0, extra, hc, hne, hq, fun hix => ?_⟩
      · rw [hv]; unfold pwByte
        rw [if_pos (by omega), show o0 + out.length + (i - out.length) - (o0 + out.length) =
          i - out.length by omega]
      · have hlt : i - out.length < ((ys.drop out.length).take xs.length).length := by
          rw [hxw]; omega
        rw [hc0 hlt, ← hpast i hiL', List.getElem_take, List.getElem_drop,
          getD_eq_getElem ys _ i (by omega)]
        congr 2; omega
  · intro i hi
    rw [List.length_append] at hi
    rw [gR i hi]; exact hpast i (by omega)

end os

end Perennial
