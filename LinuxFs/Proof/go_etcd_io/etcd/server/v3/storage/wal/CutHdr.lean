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

/-- A chain of full writes from inside the file grows its size to the end of what it wrote. -/
theorem metaChain_size {o0 : Nat} {m0 : OsMeta} {a : Nat} {m : OsMeta}
    (h : os.MetaChain o0 m0 a m) (ho : o0 ≤ m0.size) : m.size = max m0.size (o0 + a) := by
  induction h with
  | nil => omega
  | step _ hk ih =>
    simp only [pwPost, pwSize]
    rw [if_neg (by omega), ih]
    omega

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
