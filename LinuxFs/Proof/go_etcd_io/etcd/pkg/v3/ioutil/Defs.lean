/-
**A `*ioutil.PageWriter` over a stream writer** (WAL W6, 2026-11-13; the part's translation of
`pkg/v3/ioutil`, pagewriter.go): `ioutil.ownPageWriter pw wi pend`, the page writer at `pw` writing
through `wi` (an `io.writerStream wi W`, `Proof/io/WriterStream.lean`, at the callers) and holding
`pend` in its buffer: the bytes it has accepted and not yet handed to `wi`. Its specs keep
`out ++ pend` (the writer's bytes, then the buffered ones) the concatenation of everything written
to it, until an error drops the buffer.

It owns the struct and its buffer `bs` (`pend` is `bs[:bufferedBytes]`), with the facts the code
keeps (`ioutil.pwOk`): the watermark is `defaultBufferBytes` (`128 KiB`), the page size is positive
and at most the watermark (else a `Write` of a tail longer than the watermark recurses for good),
the buffer is `watermark + pageBytes` long, and the next page boundary at or after the buffered
bytes fits in the buffer: at most `watermark + pageBytes` buffered bytes if they end on a page
boundary (a `Write` fills the last page before flushing), else `bufferedBytes - (pageOffset +
bufferedBytes) % pageBytes ≤ watermark`. `pageOffset` stays below `2^62`, so that `pageOffset +
bufferedBytes` does not overflow. Lean-first.
-/
module

public import Proof.io.WriterStream
public import LinuxFs.Proof.go_etcd_io.etcd.pkg.v3.ioutil.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- The watermark, `defaultBufferBytes` (`128 * 1024`). -/
abbrev ioutil.wmBytes : Int := 131072

/-- The facts a page writer keeps (see the file header): `off`, `pB`, `bb` its `pageOffset`,
`pageBytes` and `bufferedBytes`, `len` its buffer's length. -/
def ioutil.pwOk (off pB bb : Int) (len : Nat) : Prop :=
  0 < pB ∧ pB ≤ ioutil.wmBytes ∧ 0 ≤ off ∧ off < 2 ^ 62 ∧ 0 ≤ bb ∧
    ((off + bb) % pB = 0 → bb ≤ ioutil.wmBytes + pB) ∧
    ((off + bb) % pB ≠ 0 → bb - (off + bb) % pB ≤ ioutil.wmBytes) ∧
    (len : Int) = ioutil.wmBytes + pB

/-- Below the watermark, the page writer's facts hold whatever the alignment. -/
theorem ioutil.pwOk_of_le {off pB bb : Int} {len : Nat} (h1 : 0 < pB) (h2 : pB ≤ ioutil.wmBytes)
    (h3 : 0 ≤ off) (h4 : off < 2 ^ 62) (h5 : 0 ≤ bb) (h6 : bb ≤ ioutil.wmBytes)
    (h7 : (len : Int) = ioutil.wmBytes + pB) : ioutil.pwOk off pB bb len := by
  have := Int.emod_nonneg (off + bb) (by omega : pB ≠ 0)
  exact ⟨h1, h2, h3, h4, h5, fun _ => by omega, fun _ => by omega, h7⟩

/-- The buffered bytes fit in the buffer. -/
theorem ioutil.pwOk_bb_le {off pB bb : Int} {len : Nat} (h : ioutil.pwOk off pB bb len) :
    bb ≤ ioutil.wmBytes + pB := by
  obtain ⟨h1, -, -, -, -, hal, hun, -⟩ := h
  have := Int.emod_lt_of_pos (off + bb) h1
  by_cases hc : (off + bb) % pB = 0
  · exact hal hc
  · have := hun hc; omega

/-- `(a + l) % p` when `a % p + l` stays below `p`. -/
theorem ioutil.emod_add_small (a l p : Int) (hp : 0 < p) (hl : 0 ≤ l) (h : a % p + l < p) :
    (a + l) % p = a % p + l := by
  have e : a + l = (a % p + l) + p * (a / p) := by
    have := Int.emod_add_mul_ediv a p; omega
  rw [e, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (by have := Int.emod_nonneg a (by omega : p ≠ 0); omega) h

/-- Go's `a % b` on non-negative `int`s is the Euclidean remainder. -/
theorem ioutil.sint_srem (a b : w64) (ha : 0 ≤ sint.Z a) :
    sint.Z (BitVec.srem a b) = sint.Z a % sint.Z b := by
  rw [show sint.Z (BitVec.srem a b) = (BitVec.srem a b).toInt from rfl, BitVec.toInt_srem]
  exact Int.tmod_eq_emod_of_nonneg ha

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- See the file header. -/
def ioutil.ownPageWriter (pw : Loc) (wi : GoInterfaceOk) (pend : List w8) : IProp GF :=
  iprop(∃ (v : go_etcd_io.etcd.pkg.v3.ioutil.PageWriter) (bs : List w8),
    pw ↦ v ∗ v.buf' ↦* bs ∗
    ⌜v.w' = GoInterface.ok wi ∧ v.bufWatermarkBytes' = W64 131072 ∧
      ioutil.pwOk (sint.Z v.pageOffset') (sint.Z v.pageBytes') (sint.Z v.bufferedBytes')
        bs.length ∧
      pend = bs.take (sint.nat v.bufferedBytes')⌝)

end defs

end EtcdGrove
end Perennial
