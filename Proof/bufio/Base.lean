/-
**Helpers of `bufio`'s proofs** (dsv-bufio, 2026-11-23): slice lemmas and the specs of the small
methods the specified ones call (`(*Reader).{readErr,Buffered,reset}`, `(*Writer).{Available,
Buffered}`) and of the builtin `max` of two `int`s, which `NewReaderSize` calls. Ported from
dsverify-lab's `Harness/Proof/bufio/{Reader,Writer}.lean` and `Harness/Proof/net/rpc/Wire.lean`
(`ownSlice_drop_acc`, `ownSlice_sub_acc`), and moved here from `Proof/bufio/{Reader__Read,
NewReader}.lean` (`wp_readErr`, `wp_Buffered`, `wp_max_int`). The slice lemmas are facts about
Perennial's slices that belong to Perennial (`notes/perennial-changes.md`, 2026-11-23).
-/
module

public import GeneratedProof.bufio
public import Perennial.Proof.ProofPrelude

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section lemmas

theorem bufio.sint_Z_W64_length {n : Nat} (h : n < 2 ^ 63) : sint.Z (W64 n) = n := by
  have : ((n : Int) : w64).toInt = (n : Int) := by
    rw [BitVec.toInt_intCast]; apply Int.bmod_eq_of_le <;> omega
  exact this

/-- The buffer after `Flush`'s `copy(b.buf[0:b.n-n], b.buf[n:b.n])` (`wp_slice_copy_within`):
the unsent bytes moved to the front. -/
theorem bufio.flush_shift (pend rest : List w8) (k : Nat) (hk : k ≤ pend.length) :
    (pend ++ rest).take 0 ++
      ((subslice k pend.length (pend ++ rest)).take (pend.length - k - 0) ++
        (subslice 0 (pend.length - k) (pend ++ rest)).drop (pend.length - k)) ++
      (pend ++ rest).drop (pend.length - k) =
    pend.drop k ++ (pend ++ rest).drop (pend.length - k) := by
  have h1 : subslice k pend.length (pend ++ rest) = pend.drop k := by
    rw [subslice_def, List.take_left]
  have h2 : (subslice 0 (pend.length - k) (pend ++ rest)).drop (pend.length - k) = [] := by
    apply List.drop_eq_nil_of_le
    rw [subslice_length']
    simp; omega
  rw [h1, h2, Nat.sub_zero, List.take_zero, List.take_of_length_le (by simp)]
  simp

/-- A byte stored just after the buffered bytes. -/
theorem bufio.set_after (pend rest : List w8) (c : w8) (h : rest ≠ []) :
    (pend ++ rest).set pend.length c = pend ++ [c] ++ rest.tail := by
  cases rest with
  | nil => exact absurd rfl h
  | cons x rest => simp [List.set_append_right]

end lemmas

section slices
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A prefix of an allowed stream is allowed. -/
theorem bufio.Q_of_prefix (Q : List w8 → IProp GF) (x y : List w8) (h : x <+: y) :
    iprop(□ (∀ (x y : List w8), □ Q (x ++ y) -∗ Q x)) ⊢ □ Q y -∗ □ Q x := by
  obtain ⟨z, rfl⟩ := h
  iintro #Hpc #Hy
  imodintro
  iapply Hpc $$ Hy

/-- Split a slice holding `data ++ rest` at `len(data)`: its suffix `b[len(data):len(b)]` holds
`rest`, and gives back the whole slice with any `rest'` of `rest`'s length. -/
theorem bufio.ownSlice_drop_acc {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (b : GoSlice) (dq : DFrac) (data rest : List V) :
    (b ↦*{dq} (data ++ rest) : IProp GF) ⊢
      ⌜sint.Z (W64 data.length) = data.length ∧ sint.Z b.len = data.length + rest.length⌝ ∗
      slice.slice b V (W64 data.length) b.len ↦*{dq} rest ∗
      (∀ rest' : List V, ⌜rest'.length = rest.length⌝ -∗
        slice.slice b V (W64 data.length) b.len ↦*{dq} rest' -∗ b ↦*{dq} (data ++ rest')) := by
  iintro Hb
  ihave %Hl := ownSlice_len _ _ _ $$ Hb
  have h63 : sint.Z b.len < 2 ^ 63 := by word
  have hlen : data.length + rest.length = (sint.Z b.len).toNat := by
    rw [← List.length_append]; exact Hl.1
  have hZ : sint.Z (W64 data.length) = data.length := bufio.sint_Z_W64_length (by omega)
  have hN : sint.nat (W64 data.length) = data.length := by
    show (sint.Z (W64 data.length)).toNat = _; rw [hZ]; rfl
  have h0 : sint.Z (W64 0) = 0 := rfl
  ihave Hsplit := (ownSlice_split_all (W64 data.length) b dq _
    ⟨by rw [hZ]; omega, by rw [hZ]; omega⟩).1 $$ Hb
  rw [hN, List.take_left' rfl, List.drop_left' rfl]
  icases Hsplit with ⟨Hpre, Hrest⟩
  isplitr
  · ipureintro; exact ⟨hZ, by omega⟩
  iframe Hrest
  iintro %rest' %Hr Hrest
  iapply ownSlice_trivial_slice_2
  iapply ownSlice_combine (W64 data.length) b dq data rest' (W64 0) b.len
    ⟨by rw [hN]; rfl, by rw [h0]; omega, by rw [h0, hZ]; omega, by rw [hZ]; omega⟩ $$ Hpre Hrest

/-- A sub-slice `p[lo:hi]` of a slice, and the way back. -/
theorem bufio.ownSlice_sub_acc {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (lo hi : w64) (p : GoSlice) (dq : DFrac) (vs : List V)
    (hb : 0 ≤ sint.Z lo ∧ sint.Z lo ≤ sint.Z hi ∧ sint.Z hi ≤ sint.Z p.len) :
    (p ↦*{dq} vs : IProp GF) ⊢
      slice.slice p V lo hi ↦*{dq} subslice (sint.nat lo) (sint.nat hi) vs ∗
      (slice.slice p V lo hi ↦*{dq} subslice (sint.nat lo) (sint.nat hi) vs -∗ p ↦*{dq} vs) := by
  iintro Hp
  icases (ownSlice_slice lo hi p dq vs hb).1 $$ Hp with ⟨H0, H1, H2⟩
  iframe H1
  iintro H1
  iapply (ownSlice_slice lo hi p dq vs hb).2
  iframe

/-- The suffix `buf[w:]` of a buffer holding `pre ++ rest` with `w = len(pre)`, and the way
back with any `rest'` of `rest`'s length. -/
theorem bufio.suffix_acc (buf : GoSlice) (w : w64) (pre rest : List w8)
    (hw : sint.Z w = pre.length) :
    (buf ↦* (pre ++ rest) : IProp GF) ⊢
      ⌜sint.Z buf.len = pre.length + rest.length⌝ ∗
      slice.slice buf w8 w buf.len ↦* rest ∗
      (∀ rest' : List w8, ⌜rest'.length = rest.length⌝ -∗
        slice.slice buf w8 w buf.len ↦* rest' -∗ buf ↦* (pre ++ rest')) := by
  iintro Hb
  ihave %Hl := ownSlice_len _ _ _ $$ Hb
  have h63 : sint.Z buf.len < 2 ^ 63 := by word
  have hl : pre.length + rest.length = (sint.Z buf.len).toNat := by
    rw [← List.length_append]; exact Hl.1
  have hw' : w = W64 pre.length := by
    apply BitVec.eq_of_toInt_eq
    rw [show BitVec.toInt w = sint.Z w from rfl, hw]
    have : ((pre.length : Int) : w64).toInt = (pre.length : Int) := by
      rw [BitVec.toInt_intCast]; apply Int.bmod_eq_of_le
      · omega
      · omega
    exact this.symm
  subst hw'
  ihave ⟨%Hsz, Hsuf, Hback⟩ := bufio.ownSlice_drop_acc buf _ pre rest $$ Hb
  iframe Hsuf Hback
  ipureintro; exact Hsz.2

/-- `ownSlice_trivial_slice` with the literal `0`. -/
theorem bufio.whole_slice (s : GoSlice) (dq : DFrac) (vs : List w8) :
    (s ↦*{dq} vs : IProp GF) ⊣⊢ slice.slice s w8 0 s.len ↦*{dq} vs := by
  rw [show (0 : w64) = W64 0 from rfl]; exact ownSlice_trivial_slice s dq vs

/-- `p = p[k:]` on the rest `ps.drop j` of the stream, and the way back to `P`. -/
theorem bufio.slice_advance (pc : GoSlice) (dq : DFrac) (ps : List w8) (j k : Nat)
    (hk : k ≤ (ps.drop j).length) (P : IProp GF) :
    (pc ↦*{dq} ps.drop j ∗ (pc ↦*{dq} ps.drop j -∗ P) : IProp GF) ⊢
      ⌜sint.Z (W64 k) = k⌝ ∗ slice.slice pc w8 (W64 k) pc.len ↦*{dq} ps.drop (j + k) ∗
      (slice.slice pc w8 (W64 k) pc.len ↦*{dq} ps.drop (j + k) -∗ P) := by
  iintro ⟨Hpc, Hback⟩
  have hsp : ps.drop j = (ps.drop j).take k ++ ps.drop (j + k) := by
    rw [← List.drop_drop, List.take_append_drop]
  have hl : ((ps.drop j).take k).length = k := by simp; simp at hk; omega
  rw [hsp]
  ihave ⟨%Hsz, Hsuf, Hb2⟩ := bufio.ownSlice_drop_acc pc dq ((ps.drop j).take k) (ps.drop (j + k))
    $$ Hpc
  rw [hl] at Hsz
  rw [hl]
  iframe Hsuf
  isplitr
  · ipureintro; exact Hsz.1
  iintro H
  iapply Hback
  iapply Hb2 $$ %_ %rfl H

end slices

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

/-- `b.readErr()`: the pending error, cleared. -/
theorem bufio.wp_readErr (b : Loc) (v : _root_.Perennial.bufio.Reader) :
    {{ (b ↦ v : IProp GF) }}
      (App (Val (b @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"readErr"))
        (Val #()))
    {{ RET #v.err'; b ↦ { v with err' := GoInterface.nil } }} := by
  wp_start as Hv
  try wp_auto
  iapply HΦ
  iexact Hv

/-- `b.Buffered()`: `w - r`. -/
theorem bufio.wp_Buffered (b : Loc) (v : _root_.Perennial.bufio.Reader) :
    {{ (b ↦ v : IProp GF) }}
      (App (Val (b @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"Buffered"))
        (Val #()))
    {{ RET #(v.w' - v.r'); b ↦ v }} := by
  wp_start as Hv
  try wp_auto
  iapply HΦ
  iexact Hv

/-- `b.reset(buf, rd)`: a fresh reader over `rd` with the buffer `buf`. -/
theorem bufio.wp_reset (b : Loc) (v : _root_.Perennial.bufio.Reader) (buf : GoSlice)
    (rd : GoInterface) :
    {{ (b ↦ v : IProp GF) }}
      (App (App (Val (b @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"reset"))
        (Val #buf)) (Val #rd))
    {{ RET #(); b ↦ _root_.Perennial.bufio.Reader.mk buf rd 0 0 interface.nil (W64 (-1))
        (W64 (-1)) }} := by
  wp_start as Hb
  wp_auto
  iapply HΦ $$ Hb

/-- `b.Available()`: `len(buf) - n`. -/
theorem bufio.wp_Writer_Available (bw : Loc) (v : _root_.Perennial.bufio.Writer) :
    {{ (bw ↦ v : IProp GF) }}
      (App (Val (bw @!! go.GoType.PointerType _root_.Perennial.bufio.Writer.ty @!! go!"Available"))
        (Val #()))
    {{ RET #(v.buf'.len - v.n'); bw ↦ v }} := by
  wp_start as Hb
  wp_auto
  iapply HΦ $$ Hb

/-- `b.Buffered()` of a writer: `n`. -/
theorem bufio.wp_Writer_Buffered (bw : Loc) (v : _root_.Perennial.bufio.Writer) :
    {{ (bw ↦ v : IProp GF) }}
      (App (Val (bw @!! go.GoType.PointerType _root_.Perennial.bufio.Writer.ty @!! go!"Buffered"))
        (Val #()))
    {{ RET #v.n'; bw ↦ v }} := by
  wp_start as Hb
  wp_auto
  iapply HΦ $$ Hb

/-- The builtin `max` of two `int`s: the larger. -/
theorem bufio.wp_max_int (x y : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.max [go.int, go.int])) (Val #x)) (Val #y))
    {{ (m : w64), RET #m; ⌜(m = x ∨ m = y) ∧ sint.Z x ≤ sint.Z m ∧ sint.Z y ≤ sint.Z m⌝ }} := by
  wp_start
  wp_if_destruct
  · iapply HΦ; ipureintro; refine ⟨Or.inl rfl, Int.le_refl _, ?_⟩; word
  · iapply HΦ; ipureintro; refine ⟨Or.inr rfl, ?_, Int.le_refl _⟩; word

end wps

end EtcdGrove
end Perennial
