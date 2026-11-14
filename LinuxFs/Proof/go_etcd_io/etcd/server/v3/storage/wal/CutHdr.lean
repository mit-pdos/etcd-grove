/- Lean-first (no Rocq counterpart).

# The new segment after `cut`'s header phase (W2, step 5; pure)

`cut` writes the new segment's headers into the pipeline's `N.tmp` (zeros, owned wholly) through
`os.File.writerStream` from offset 0, then fdatasyncs it (`os.fileS`). What `walCut_osAUnc` needs of
the result: the bytes are the headers then zeros, all durable; the `OsMeta`'s size is the larger of
the old size and the headers', its `cut` the old one.

* `metaChain_cut`, `metaChain_size`: a chain of full writes keeps the `cut` and grows the size to
  the end of what it wrote.
* `streamOk_vals`: over zeros, the bytes after the stream are its bytes then zeros.
-/
module

public import LinuxFs.Proof.os.WriterStream

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs

/-- A chain of full writes keeps the `cut`. -/
theorem metaChain_cut {o0 : Nat} {m0 : OsMeta} {a : Nat} {m : OsMeta}
    (h : os.MetaChain o0 m0 a m) : m.cut = m0.cut := by
  induction h with
  | nil => rfl
  | step _ _ ih => simp only [pwPost, OsMeta.announce_cut]; exact ih

/-- **The zeros known past a file's size, with its page cache zero to the end of their page**
(W6 log, sixteenth session, finding 1): `zf = some z` (at least the size, `MetaOk.zf`), and the page
cache known zero (`cz`) to the end of the page holding `z`, or `z` page-aligned at the size. A chain of
full writes from inside the file keeps it (`metaChain_zeroPg`: a write landing up to `z` raises `cz`,
`Fs.pwCz`), and with it a sync leaves the zeros known from the size on (`OsMeta.syncZ` the size). -/
def ZeroPg (m : OsMeta) : Prop := ∃ z, m.zf = some z ∧ m.size ≤ z ∧ pageEnd z ≤ max m.size m.cz

theorem ZeroPg.pageEnd_size {m : OsMeta} (h : ZeroPg m) : pageEnd m.size ≤ max m.size m.cz := by
  obtain ⟨z, -, h1, h2⟩ := h
  exact Nat.le_trans (pageEnd_mono h1) h2

/-- A full write of `n > 0` bytes at `off ≤ size` keeps `ZeroPg`. -/
theorem ZeroPg.write {m : OsMeta} {off n : Nat} (h : ZeroPg m) (hoff : off ≤ m.size) (hn : 0 < n) :
    ZeroPg (pwPost m off n n) := by
  obtain ⟨z, hz, h1, h2⟩ := h
  have hmin : min off m.size = off := Nat.min_eq_left hoff
  have hzf : (pwPost m off n n).zf = some (max z (off + n)) := by
    simp only [pwPost, announce_zf, hz, hmin, Option.map_some]; rw [if_pos (by omega)]
  have hsz : (pwPost m off n n).size = max m.size (off + n) := by
    simp only [pwPost, pwSize]; rw [if_neg (by omega)]
  have hcz : (pwPost m off n n).cz = pwCz m off n n := rfl
  refine ⟨_, hzf, by rw [hsz]; omega, ?_⟩
  rw [hsz, hcz]
  have hle := le_pwCz m off n n
  by_cases hzk : z ≤ off + n
  · have := pwCz_raise hz hn hzk
    rw [show max z (off + n) = off + n by omega]; omega
  · rw [show max z (off + n) = z by omega]; omega

/-- A chain of full writes from inside the file grows its size to the end of what it wrote. -/
theorem metaChain_size {o0 : Nat} {m0 : OsMeta} {a : Nat} {m : OsMeta}
    (h : os.MetaChain o0 m0 a m) (ho : o0 ≤ m0.size) : m.size = max m0.size (o0 + a) := by
  induction h with
  | nil => omega
  | step _ hk ih =>
    simp only [pwPost, pwSize]
    rw [if_neg (by omega), ih]
    omega

/-- A chain of full writes from inside the file keeps `ZeroPg` (the zeros known past the size, the
page cache zero to their page's end). -/
theorem metaChain_zeroPg {o0 : Nat} {m0 : OsMeta} {a : Nat} {m : OsMeta}
    (h : os.MetaChain o0 m0 a m) (ho : o0 ≤ m0.size) (hz : ZeroPg m0) : ZeroPg m := by
  induction h with
  | nil => exact hz
  | step hc hk ih =>
    have hs := metaChain_size hc ho
    exact ih.write (by rw [hs]; omega) hk

/-- **The bytes after a stream over zeros from offset 0**: its bytes, then zeros. -/
theorem streamOk_vals {m0 : OsMeta} {xs0 : List ByteG} {out : List w8} {m : OsMeta}
    {ys : List ByteG} (h : os.StreamOk m0 0 xs0 out m ys) (hz : ∀ x ∈ xs0, x.1 = 0) :
    ys.map (fun x => durB x.1) =
      (out ++ List.replicate (ys.length - out.length) 0).map durB ∧ out.length ≤ ys.length := by
  obtain ⟨-, -, -, -, -, hol, hyl, hin, hout⟩ := h
  have hle : out.length ≤ ys.length := by omega
  refine ⟨?_, hle⟩
  apply List.ext_getElem
  · simp; omega
  intro i h1 h2
  have h1' : i < ys.length := by simpa using h1
  simp only [List.getElem_map]
  congr 1
  have hgi : ys[i] = ys.getD i (0, []) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1']; rfl
  rw [hgi]
  by_cases hi : i < out.length
  · rw [(hin i hi).1, List.getElem_append_left hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi]
    rfl
  · rw [hout i (by omega), List.getElem_append_right (by omega), List.getElem_replicate]
    rw [List.getD_eq_getElem?_getD]
    cases hx : xs0[i]? with
    | none => rfl
    | some x => exact hz x (List.mem_of_getElem? hx)

end WalFs
end EtcdGrove
end Perennial

end
