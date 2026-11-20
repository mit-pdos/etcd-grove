/-
The specs of `bufio.Writer` (Go's code, `Harness/Code/bufio.lean`) over an underlying
`io.Writer` given by its spec (`writerOk`, `Defs.lean`), and their proofs. The writer buffers:
bytes reach the underlying writer only when the buffer fills or on `Flush`, as a prefix of what
was written, in order; an error of the underlying writer sticks (`ownWriter`'s `err`).

* `NewWriter(wr)`: a fresh `*Writer` over `wr` that has sent `W` and buffers nothing.
* `(*Writer).Flush()`: sends a prefix `pend.take k` of the buffered bytes; all of them when it
  returns `nil`; with a sticky error, nothing, and the error.
* `(*Writer).Write(p)`: accepts the first `k` bytes of `p` (all of them when it returns `nil`;
  none with a sticky error); some prefix of the accepted bytes has been sent, the rest is
  buffered.
* `(*Writer).WriteByte(c)`: accepts `c` when it returns `nil`; nothing otherwise.
Each write needs `□ Q (sent ++ pend ++ new)`: the stream with the new bytes is allowed.
-/
module

public import Harness.Proof.bufio.Defs
public import Harness.Proof.bufio.Reader

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace bufio

section lemmas

/-- The buffer after `Flush`'s `copy(b.buf[0:b.n-n], b.buf[n:b.n])` (`wp_slice_copy_within`):
the unsent bytes moved to the front. -/
theorem flush_shift (pend rest : List w8) (k : Nat) (hk : k ≤ pend.length) :
    (pend ++ rest).take 0 ++
      ((subslice k pend.length (pend ++ rest)).take (pend.length - k - 0) ++
        (subslice 0 (pend.length - k) (pend ++ rest)).drop (pend.length - k)) ++
      (pend ++ rest).drop (pend.length - k) =
    pend.drop k ++ (pend ++ rest).drop (pend.length - k) := by
  have h1 : subslice k pend.length (pend ++ rest) = pend.drop k := by
    rw [subslice_def, List.take_left]
  have h2 : (subslice 0 (pend.length - k) (pend ++ rest)).drop (pend.length - k) = [] := by
    apply List.drop_eq_nil_of_le
    rw [subslice_length' ]
    simp; omega
  rw [h1, h2, Nat.sub_zero, List.take_zero, List.take_of_length_le (by simp)]
  simp

/-- A byte stored just after the buffered bytes. -/
theorem set_after (pend rest : List w8) (c : w8) (h : rest ≠ []) :
    (pend ++ rest).set pend.length c = pend ++ [c] ++ rest.tail := by
  cases rest with
  | nil => exact absurd rfl h
  | cons x rest => simp [List.set_append_right]

variable [GooseExts] [GooseSemantics] [GooseInterp]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- A prefix of an allowed stream is allowed. -/
theorem Q_of_prefix (Q : List w8 → IProp GF) (x y : List w8) (h : x <+: y) :
    prefixClosed Q ⊢ □ Q y -∗ □ Q x := by
  obtain ⟨z, rfl⟩ := h
  iintro #Hpc #Hy
  iunfold prefixClosed at Hpc
  imodintro
  iapply Hpc $$ Hy

variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- `p = p[k:]` on the rest `ps.drop j` of the stream, and the way back to `P`. -/
theorem slice_advance (pc : GoSlice) (dq : DFrac) (ps : List w8) (j k : Nat)
    (hk : k ≤ (ps.drop j).length) (P : IProp GF) :
    (pc ↦*{dq} ps.drop j ∗ (pc ↦*{dq} ps.drop j -∗ P) : IProp GF) ⊢
      ⌜sint.Z (W64 k) = k⌝ ∗ slice.slice pc w8 (W64 k) pc.len ↦*{dq} ps.drop (j + k) ∗
      (slice.slice pc w8 (W64 k) pc.len ↦*{dq} ps.drop (j + k) -∗ P) := by
  iintro ⟨Hpc, Hback⟩
  have hsp : ps.drop j = (ps.drop j).take k ++ ps.drop (j + k) := by
    rw [← List.drop_drop, List.take_append_drop]
  have hl : ((ps.drop j).take k).length = k := by simp; simp at hk; omega
  rw [hsp]
  ihave ⟨%Hsz, Hsuf, Hb2⟩ := net.rpc.ownSlice_drop_acc pc dq ((ps.drop j).take k) (ps.drop (j + k))
    $$ Hpc
  rw [hl] at Hsz
  rw [hl]
  iframe Hsuf
  isplitr
  · ipureintro; exact Hsz.1
  iintro H
  iapply Hback
  iapply Hb2 $$ %_ %rfl H

/-- `copy(dst, src)` with the count as a signed integer (`wp_slice_copy` gives its `sint.nat`,
which says nothing of its sign when the count is `0`). -/
theorem wp_slice_copy_Z {st t : go.GoType} [st ↓u go.SliceType t] {V : Type}
    [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t]
    (sl : GoSlice) (vs : List V) (sl2 : GoSlice) (vs' : List V) (dq : DFrac) :
    {{ (sl ↦* vs ∗ sl2 ↦*{dq} vs' : IProp GF) }}
      (App (App (Val #(functions go.copy [st])) (Val #sl)) (Val #sl2))
    {{ (n : w64), RET #n; ⌜sint.Z n = min vs.length vs'.length⌝ ∗
        sl ↦* (vs'.take vs.length ++ vs.drop vs'.length) ∗ sl2 ↦*{dq} vs' }} := by
  iintro %Φ ⟨Hs1, Hs2⟩ HΦ
  ihave %Hlen1 := ownSlice_len _ _ _ $$ Hs1
  ihave %Hlen2 := ownSlice_len _ _ _ $$ Hs2
  by_cases h2 : vs' = []
  · subst h2
    have hz : sl2.len = W64 0 := by
      apply BitVec.eq_of_toInt_eq
      show sint.Z sl2.len = sint.Z (W64 0)
      have : sint.Z (W64 0) = 0 := rfl
      have : (sint.Z sl2.len).toNat = 0 := by simpa using Hlen2.1.symm
      omega
    wp_apply wp_slice_copy_of_len_zero (V := V) sl sl2 hz
    iapply HΦ
    simp only [List.length_nil, Nat.min_zero, List.take_nil, List.drop_zero, List.nil_append]
    iframe Hs1 Hs2
    ipureintro; rfl
  by_cases h1 : vs = []
  · subst h1
    have hz : sl.len = W64 0 := by
      apply BitVec.eq_of_toInt_eq
      show sint.Z sl.len = sint.Z (W64 0)
      have : sint.Z (W64 0) = 0 := rfl
      have : (sint.Z sl.len).toNat = 0 := by simpa using Hlen1.1.symm
      omega
    wp_func_call
    wp_call
    wp_apply wp_slice_make2 (V := V) sl2.len $$ [] as %tmp ⟨Htmp, _⟩
    · ipureintro; exact Hlen2.2
    wp_apply wp_copyForward tmp _ sl2 vs' dq $$ [Htmp Hs2] as %n1 ⟨_, Htmp, Hs2⟩
    · iframe
    wp_apply wp_copyForward_len_zero (V := V) sl tmp (.inl hz)
    iapply HΦ
    simp only [List.length_nil, Nat.zero_min, List.take_zero, List.drop_nil, List.nil_append]
    iframe Hs1 Hs2
    ipureintro; rfl
  wp_apply wp_slice_copy (V := V) sl vs sl2 vs' dq $$ [$Hs1 $Hs2] as %n ⟨%Hn, Hs1, Hs2⟩
  iapply HΦ
  iframe Hs1 Hs2
  ipureintro
  have : 0 < min vs.length vs'.length :=
    Nat.lt_min.mpr ⟨List.length_pos_iff.mpr h1, List.length_pos_iff.mpr h2⟩
  have : (sint.Z n).toNat = min vs.length vs'.length := Hn
  omega

end lemmas

set_option hygiene false in
/-- The end of `Flush` after a failed write of `k` bytes (`Hst`: the unsent bytes at the front
of the buffer). -/
local macro "flush_tail" : tactic => `(tactic| (
  icases Hst with ⟨%rest', Hbuf, %Hr'⟩
  (try wp_auto)
  isimp at Hb
  iapply HΦ
  iexists k
  isplitr
  · ipureintro; exact ⟨Hk.1, by simp, by simp⟩
  iunfold ownWriter, writerRep
  rw [List.append_assoc sent, List.take_append_drop]
  iframe HJ HQ
  iexists buf, _, rest'
  iframe Hb Hbuf Herr2
  ipureintro
  constructor
  · simp only [List.length_drop]; word
  · rw [Hr']; exact Hn.2))

set_option hygiene false in
/-- The end of `WriteByte`: store `c` after the buffered bytes `pend0` (`Hn0`, `Hr0`: room
left; `Hpre`, `Heq`: `sent0 ++ pend0` is what was written). -/
local macro "writebyte_tail" sent0:term:max pend0:term:max rest0:term:max buf0:term:max
    n0:term:max : tactic => `(tactic| (
  ihave %Hl0 := ownSlice_len _ _ _ $$ Hbuf
  have hl0 : (($pend0 ++ $rest0).length : Int) = sint.Z ($buf0).len := by
    rw [Hl0.1]; exact Int.toNat_of_nonneg Hl0.2
  simp only [List.length_append] at hl0
  have hrl : 0 < ($rest0).length := List.length_pos_iff.mpr Hr0
  (try wp_auto)
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
  wp_apply wp_store_slice_index $buf0 (sint.Z $n0) ($pend0 ++ $rest0) c $$ [Hbuf] as Hbuf
  · iframe Hbuf; ipureintro; simp; omega
  rw [show (sint.Z $n0).toNat = ($pend0).length by omega, set_after $pend0 $rest0 c Hr0]
  (try isimp at Hb)
  iapply HΦ
  iexists $sent0, $pend0 ++ [c]
  isplitr
  · ipureintro
    exact ⟨Hpre, fun _ => by rw [← List.append_assoc, Heq], fun h => absurd rfl h, by simp⟩
  iunfold ownWriter, writerRep
  rw [show $sent0 ++ ($pend0 ++ [c]) = sent ++ pend ++ [c] by rw [← List.append_assoc, Heq]]
  iframe HJ HQc
  iexists $buf0, _, ($rest0).tail
  iframe Hb Hbuf Herr
  ipureintro
  constructor
  · simp only [List.length_append, List.length_singleton]; word
  · simp; omega))

set_option hygiene false in
/-- The end of `Write` with a sticky error `ok ei`: return it. -/
local macro "write_err_tail" : tactic => `(tactic| (
  wp_auto
  ihave Hp := Hpback $$ Hpc
  ihave #HQ0 := Q_of_prefix Q (sent0 ++ pend0) (sent ++ pend ++ ps)
    (by rw [hsent]; exact (List.prefix_append_right_inj _).mpr (List.take_prefix _ _))
    $$ HQpc HQall
  iapply HΦ
  iexists j, sent0, pend0
  iframe Hp
  isplitr
  · ipureintro
    exact ⟨hnnv, hj, hsent, hpre, fun h => absurd h (by simp), herr⟩
  iunfold ownWriter, writerRep
  iframe HJ HQ0
  iexists buf0, n0, rest0
  iframe Hb Hbuf Herr0
  ipureintro; exact ⟨hn0, hlen0⟩))

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions]

set_option goose.wp.extras true

theorem wp_NewWriter (wr : GoInterface) (J Q : List w8 → IProp GF) (W : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗ J W ∗ □ Q W }}
      (App (Val (@! bufio.NewWriter)) (Val #wr))
    {{ (bw : Loc), RET #bw; ownWriter bw wr J Q W [] interface.nil }} := by
  wp_start as ⟨#Hwr, HJ, #HQ⟩
  unfold writerOk
  icases Hwr with ⟨%e, %He, -, #Hw⟩
  obtain ⟨rfl, hty⟩ := He
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  simp only [hty, ↓reduceIte, decide_false]
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) _) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  iapply HΦ
  unfold ownWriter writerRep
  rw [List.append_nil]
  iframe HJ HQ
  iexists buf, 0, List.replicate 4096 (zero_val w8)
  simp only [List.nil_append, List.length_nil, List.length_replicate]
  iframe «$r0» Hbuf
  isplitr
  · ipureintro; exact ⟨rfl, by decide⟩
  unfold errOrNil
  ileft; ipureintro; rfl

/-- `Flush()`: see the file header. -/
theorem wp_Flush (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"Flush")) (Val #()))
    {{ (e : GoInterface), RET #e; ∃ k : Nat,
        ⌜k ≤ pend.length ∧ (e = interface.nil → k = pend.length) ∧
          (err ≠ interface.nil → e = err ∧ k = 0)⌝ ∗
        ownWriter bw wr J Q (sent ++ pend.take k) (pend.drop k) e }} := by
  wp_start as ⟨#Hwr, Hown⟩
  ihave #Hwr' := Hwr
  iunfold writerOk at Hwr'
  icases Hwr' with ⟨%e, %He, -, #HWrite⟩
  obtain ⟨rfl, hty⟩ := He
  iunfold ownWriter, writerRep at Hown
  icases Hown with ⟨HJ, #HQ, %buf, %n, %rest, Hb, Hbuf, %Hn, #Herr⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hbuf
  have h63 : sint.Z buf.len < 2 ^ 63 := by word
  have hl : ((pend ++ rest).length : Int) = sint.Z buf.len := by
    rw [Hlen.1]; exact Int.toNat_of_nonneg Hlen.2
  simp only [List.length_append] at hl
  rcases err with ei | _
  · -- a sticky error: return it
    wp_auto
    iapply HΦ
    iexists 0
    simp only [List.take_zero, List.append_nil, List.drop_zero]
    isplitr
    · ipureintro; simp
    iunfold ownWriter, writerRep
    iframe HJ HQ
    iexists buf, n, rest
    iframe Hb Hbuf Herr
    ipureintro; exact Hn
  wp_auto
  wp_if_destruct
  · -- nothing buffered
    have hp : pend = [] := List.eq_nil_of_length_eq_zero (by
      have : sint.Z (W64 0) = 0 := rfl
      omega)
    subst hp
    iapply HΦ
    iexists 0
    simp only [List.take_zero, List.append_nil, List.drop_nil]
    isplitr
    · ipureintro; simp
    iunfold ownWriter, writerRep
    simp only [List.append_nil]
    iframe HJ HQ
    iexists buf, _, rest
    iframe Hb Hbuf Herr
    ipureintro; exact Hn
  have hW0 : sint.Z (W64 0) = 0 := rfl
  have hn0 : sint.nat (W64 0) = 0 := rfl
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
  ihave ⟨Hsub, Hback⟩ := net.rpc.ownSlice_sub_acc (V := w8) (W64 0) n buf (DFrac.own 1)
    (pend ++ rest) ⟨by omega, by omega, by omega⟩ $$ Hbuf
  have hsub : subslice (sint.nat (W64 0)) (sint.nat n) (pend ++ rest) = pend := by
    rw [subslice_def, hn0, List.drop_zero,
      show sint.nat n = pend.length by show (sint.Z n).toNat = _; omega, List.take_left]
  rw [hsub]
  wp_auto
  wp_apply HWrite $$ HJ HQ Hsub as %k %err2 %Hk Hsub HJ #Herr2
  ihave Hbuf := Hback $$ Hsub
  have hpl : pend.length < 2 ^ 63 := by omega
  have hkZ : sint.Z (W64 k) = k := sint_Z_W64_length (by omega)
  rcases err2 with ei | _
  · -- an error: keep the unsent bytes, the error sticks
    have hn : sint.nat n = pend.length := by show (sint.Z n).toNat = _; omega
    have hk' : sint.nat (W64 k) = k := by show (sint.Z (W64 k)).toNat = _; omega
    wp_if_destruct
    all_goals
      wp_if_destruct
      · wp_if_destruct
        · -- `0 < n < b.n`: move the unsent bytes to the front
          have hnkZ : sint.Z (n - W64 k) = pend.length - k := by word
          have hnk : sint.nat (n - W64 k) = pend.length - k := by
            show (sint.Z (n - W64 k)).toNat = _; omega
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
          wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
          wp_apply wp_slice_copy_within (V := w8) buf (pend ++ rest) (W64 0) (n - W64 k) (W64 k) n
            ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ $$ Hbuf as %m ⟨-, Hbuf⟩
          ihave Hst : (∃ rest' : List w8, buf ↦* (pend.drop k ++ rest') ∗
              ⌜(pend.drop k ++ rest').length = (pend ++ rest).length⌝ : IProp GF) $$ [Hbuf]
          · iexists (pend ++ rest).drop (pend.length - k)
            rw [hn, hk', hnk]
            (try rw [hn0])
            rw [flush_shift pend rest k Hk.1]
            iframe Hbuf
            ipureintro; simp; omega
          flush_tail
        · -- `n = b.n`: nothing left
          ihave Hst : (∃ rest' : List w8, buf ↦* (pend.drop k ++ rest') ∗
              ⌜(pend.drop k ++ rest').length = (pend ++ rest).length⌝ : IProp GF) $$ [Hbuf]
          · iexists pend ++ rest
            rw [List.drop_eq_nil_of_le (by omega), List.nil_append]
            iframe Hbuf
            ipureintro; rfl
          flush_tail
      · -- `n = 0`: nothing sent
        have hk0 : k = 0 := by omega
        ihave Hst : (∃ rest' : List w8, buf ↦* (pend.drop k ++ rest') ∗
            ⌜(pend.drop k ++ rest').length = (pend ++ rest).length⌝ : IProp GF) $$ [Hbuf]
        · iexists rest
          rw [hk0, List.drop_zero]
          iframe Hbuf
          ipureintro; rfl
        flush_tail
  -- all sent
  have hk : k = pend.length := Hk.2 rfl
  subst hk
  have hnk : ¬ sint.Z (W64 pend.length) < sint.Z n := by omega
  simp only [decide_eq_false hnk]
  wp_auto
  isimp at Hb
  iapply HΦ
  iexists pend.length
  simp only [List.take_length, List.drop_length]
  isplitr
  · ipureintro; simp
  iunfold ownWriter, writerRep
  simp only [List.append_nil]
  iframe HJ HQ
  iexists buf, _, pend ++ rest
  simp only [List.nil_append]
  iframe Hb Hbuf Herr
  ipureintro; exact ⟨rfl, Hn.2⟩

theorem wp_Writer_Available (bw : Loc) (v : bufio.Writer) :
    {{ (bw ↦ v : IProp GF) }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"Available")) (Val #()))
    {{ RET #(v.buf'.len - v.n'); bw ↦ v }} := by
  wp_start as Hb
  wp_auto
  iapply HΦ $$ Hb

theorem wp_Writer_Buffered (bw : Loc) (v : bufio.Writer) :
    {{ (bw ↦ v : IProp GF) }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"Buffered")) (Val #()))
    {{ RET #v.n'; bw ↦ v }} := by
  wp_start as Hb
  wp_auto
  iapply HΦ $$ Hb

/-- `WriteByte(c)`: see the file header. -/
theorem wp_WriteByte (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) (c : w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ [c]) }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"WriteByte")) (Val #c))
    {{ (e : GoInterface), RET #e; ∃ sent' pend' : List w8,
        ⌜sent <+: sent' ∧ (e = interface.nil → sent' ++ pend' = sent ++ pend ++ [c]) ∧
          (e ≠ interface.nil → sent' ++ pend' = sent ++ pend) ∧
          (err ≠ interface.nil → e = err)⌝ ∗
        ownWriter bw wr J Q sent' pend' e }} := by
  wp_start as ⟨#Hwr, Hown, #HQc⟩
  ihave #Hwr' := Hwr
  iunfold writerOk at Hwr'
  icases Hwr' with ⟨%e, %He, -, -⟩
  obtain ⟨rfl, hty⟩ := He
  iunfold ownWriter, writerRep at Hown
  icases Hown with ⟨HJ, #HQ, %buf, %n, %rest, Hb, Hbuf, %Hn, #Herr⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  have h63 : sint.Z buf.len < 2 ^ 63 := by word
  have hl : ((pend ++ rest).length : Int) = sint.Z buf.len := by
    rw [Hlen.1]; exact Int.toNat_of_nonneg Hlen.2
  simp only [List.length_append] at hl
  rcases err with ei | _
  · -- a sticky error: return it
    wp_auto
    iapply HΦ
    iexists sent, pend
    isplitr
    · ipureintro; simp
    iunfold ownWriter, writerRep
    iframe HJ HQ
    iexists buf, n, rest
    iframe Hb Hbuf Herr
    ipureintro; exact Hn
  wp_auto
  wp_apply wp_Writer_Available $$ Hb as Hb
  have hW0 : sint.Z (W64 0) = 0 := rfl
  have hav : sint.Z (buf.len - n) = rest.length := by word
  wp_if_destruct
  · -- the buffer is full: flush it
    have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hr
    wp_apply wp_Flush bw (interface.ok e) J Q sent pend interface.nil $$ [$Hpkg $Hwr HJ HQ Hb Hbuf]
      as %e' ⟨%k, %Hk, Hown⟩
    · iunfold ownWriter, writerRep
      iframe HJ HQ
      iexists buf, n, []
      iframe Hb Hbuf Herr
      ipureintro; exact Hn
    rcases e' with ei | _
    · -- the flush failed: return the error
      iunfold ownWriter, writerRep at Hown
      icases Hown with ⟨HJ, #HQ', %buf', %n', %rest', Hb, Hbuf, %Hn', #Herr'⟩
      wp_auto
      iapply HΦ
      iexists sent ++ pend.take k, pend.drop k
      isplitr
      · ipureintro
        refine ⟨⟨_, rfl⟩, by simp, fun _ => ?_, by simp⟩
        simp
      iunfold ownWriter, writerRep
      iframe HJ HQ'
      iexists buf', n', rest'
      iframe Hb Hbuf Herr'
      ipureintro; exact Hn'
    have hk : k = pend.length := Hk.2.1 rfl
    subst hk
    wp_auto
    iunfold ownWriter, writerRep at Hown
    icases Hown with ⟨HJ, #HQ', %buf', %n', %rest', Hb, Hbuf, %Hn', #Herr'⟩
    simp only [List.take_length, List.drop_length, List.nil_append, List.length_nil,
      List.append_nil] at Hn' ⊢
    ihave Hst : (∃ (sent0 pend0 rest0 : List w8) (buf : GoSlice) (n0 : w64),
        "HJ" ∷ J sent0 ∗ "#HQ" ∷ □ Q (sent0 ++ pend0) ∗
        "Hb" ∷ bw ↦ bufio.Writer.mk interface.nil buf n0 (interface.ok e) ∗
        "Hbuf" ∷ buf ↦* (pend0 ++ rest0) ∗
        "%Hst" ∷ ⌜sint.Z n0 = pend0.length ∧ rest0 ≠ [] ∧ sent <+: sent0 ∧
          sent0 ++ pend0 = sent ++ pend⌝ : IProp GF) $$ [HJ Hb Hbuf]
    · iexists sent ++ pend, [], rest', buf', n'
      simp only [List.append_nil, List.nil_append]
      iframe HJ HQ' Hb Hbuf
      ipureintro
      refine ⟨Hn'.1, ?_, ⟨_, rfl⟩, ?_⟩
      · intro h; subst h; simp at Hn'
      · simp
    icases Hst with ⟨%sent0, %pend0, %rest0, %buf0, %n0, HJ, #HQ, Hb, Hbuf, %Hst⟩
    obtain ⟨Hn0, Hr0, Hpre, Heq⟩ := Hst
    writebyte_tail sent0 pend0 rest0 buf0 n0
  have Hr0 : rest ≠ [] := List.ne_nil_of_length_pos (by omega)
  have Hpre : sent <+: sent := List.prefix_refl _
  have Heq : sent ++ pend = sent ++ pend := rfl
  have Hn0 := Hn.1
  writebyte_tail sent pend rest buf n

/-- `Write(p)`: see the file header. -/
theorem wp_Write (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) (p : GoSlice) (dq : DFrac) (ps : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ ps) ∗ p ↦*{dq} ps }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"Write")) (Val #p))
    {{ (nn : w64) (e : GoInterface), RET (PairV #nn #e); ∃ (k : Nat) (sent' pend' : List w8),
        ⌜nn = W64 k ∧ k ≤ ps.length ∧ sent' ++ pend' = sent ++ pend ++ ps.take k ∧
          sent <+: sent' ∧ (e = interface.nil → k = ps.length) ∧
          (err ≠ interface.nil → e = err ∧ k = 0)⌝ ∗
        p ↦*{dq} ps ∗ ownWriter bw wr J Q sent' pend' e }} := by
  wp_start as ⟨#Hwr, Hown, #HQall, Hp⟩
  ihave #Hwr' := Hwr
  iunfold writerOk at Hwr'
  icases Hwr' with ⟨%e, %He, #HQpc, #HWrite⟩
  obtain ⟨rfl, hty⟩ := He
  iunfold ownWriter, writerRep at Hown
  icases Hown with ⟨HJ, -, %buf, %n, %rest, Hb, Hbuf, %Hn, #Herr⟩
  ihave %Hplen := ownSlice_len _ _ _ $$ Hp
  have hp63 : sint.Z p.len < 2 ^ 63 := by word
  have hpl : (ps.length : Int) = sint.Z p.len := by
    rw [Hplen.1]; exact Int.toNat_of_nonneg Hplen.2
  wp_auto
  ihave HL : (∃ (j : Nat) (nnv : w64) (pc : GoSlice) (sent0 pend0 rest0 : List w8)
      (buf0 : GoSlice) (n0 : w64) (err0 : GoInterface),
      "nn" ∷ nn_ptr ↦ nnv ∗ "p" ∷ p_ptr ↦ pc ∗ "Hpc" ∷ pc ↦*{dq} ps.drop j ∗
      "Hpback" ∷ (pc ↦*{dq} ps.drop j -∗ p ↦*{dq} ps) ∗ "HJ" ∷ J sent0 ∗
      "Hb" ∷ bw ↦ bufio.Writer.mk err0 buf0 n0 (interface.ok e) ∗
      "Hbuf" ∷ buf0 ↦* (pend0 ++ rest0) ∗ "#Herr0" ∷ errOrNil err0 ∗
      "%Hinv" ∷ ⌜sint.Z nnv = j ∧ j ≤ ps.length ∧ sint.Z n0 = pend0.length ∧
        0 < (pend0 ++ rest0).length ∧ sent0 ++ pend0 = sent ++ pend ++ ps.take j ∧
        sent <+: sent0 ∧ (err ≠ interface.nil → err0 = err ∧ j = 0)⌝ : IProp GF)
    $$ [nn p Hp HJ Hb Hbuf]
  · iexists 0, _, p, sent, pend, rest, buf, n, err
    simp only [List.drop_zero, List.take_zero, List.append_nil]
    iframe nn p Hp HJ Hb Hbuf Herr
    isplitr
    · iintro H; iexact H
    ipureintro
    exact ⟨by first | rfl | trivial, Nat.zero_le _, Hn.1, Hn.2, by first | rfl | trivial,
      List.prefix_refl _, fun _ => ⟨by first | rfl | trivial, by first | rfl | trivial⟩⟩
  clear Hn
  wp_for HL
  obtain ⟨hnn, hj, hn0, hlen0, hsent, hpre, herr⟩ := Hinv
  ihave %Hpcl := ownSlice_len _ _ _ $$ Hpc
  ihave %Hl0 := ownSlice_len _ _ _ $$ Hbuf
  have hpcl : ((ps.drop j).length : Int) = sint.Z pc.len := by
    rw [Hpcl.1]; exact Int.toNat_of_nonneg Hpcl.2
  have hl0 : ((pend0 ++ rest0).length : Int) = sint.Z buf0.len := by
    rw [Hl0.1]; exact Int.toNat_of_nonneg Hl0.2
  simp only [List.length_append, List.length_drop] at hl0 hpcl
  have hb63 : sint.Z buf0.len < 2 ^ 63 := by word
  wp_apply wp_Writer_Available $$ Hb as Hb
  have hav : sint.Z (buf0.len - n0) = rest0.length := by word
  have hnnv : nnv = W64 j := by
    apply BitVec.eq_of_toInt_eq
    show sint.Z nnv = sint.Z (W64 j)
    rw [hnn, sint_Z_W64_length (by omega)]
  wp_if_destruct
  · -- more than fits
    have hmore : rest0.length < ps.length - j := by omega
    rcases err0 with ei | _
    · -- a sticky error: done
      wp_auto
      simp only [goose_wp_simp_extra, Bool.false_eq_true, ↓reduceIte]
      write_err_tail
    wp_auto
    simp only [goose_wp_simp_extra, ↓reduceIte]
    wp_auto
    ihave %Hpwf := ownSlice_wf _ _ _ $$ Hpc
    wp_apply wp_Writer_Buffered $$ Hb as Hb
    wp_if_destruct
    · -- nothing buffered: write `p` directly
      have hp0 : pend0 = [] := List.eq_nil_of_length_eq_zero (by
        have : sint.Z (W64 0) = 0 := rfl
        omega)
      subst hp0
      simp only [List.append_nil] at hsent
      ihave #HQw := Q_of_prefix Q (sent0 ++ ps.drop j) (sent ++ pend ++ ps)
        (by rw [hsent, List.append_assoc (sent ++ pend), List.take_append_drop]
            exact List.prefix_refl _) $$ HQpc HQall
      wp_apply HWrite $$ HJ HQw Hpc as %k %err2 %Hk Hpc HJ #Herr2
      have hdl : (ps.drop j).length = ps.length - j := List.length_drop
      have hkZ : sint.Z (W64 k) = k := sint_Z_W64_length (by omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
      ihave ⟨-, Hpc, Hpback⟩ := slice_advance pc dq ps j k Hk.1 _ $$ [$Hpc $Hpback]
      wp_auto
      wp_for_post
      isimp at Hb
      iframe
      iexists j + k, _, _, sent0 ++ (ps.drop j).take k, [], rest0, buf0, _, err2
      simp only [List.append_nil, List.nil_append]
      iframe Hpc Hpback HJ Hb Hbuf Herr2 nn p
      ipureintro
      refine ⟨by word, by omega, hn0, hlen0, ?_, hpre.trans (List.prefix_append _ _),
        fun h => absurd (herr h).1.symm h⟩
      rw [hsent, List.take_add, List.append_assoc]
    -- something buffered: fill the buffer, flush it
    have hp0 : 0 < pend0.length := by
      rcases Nat.eq_zero_or_pos pend0.length with h | h
      · exfalso; apply Hif; apply BitVec.eq_of_toInt_eq
        show sint.Z n0 = sint.Z (W64 0)
        rw [hn0, h]; rfl
      · exact h
    have hdl : (ps.drop j).length = ps.length - j := List.length_drop
    ihave %Hbwf := ownSlice_wf _ _ _ $$ Hbuf
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, Hbwf.2⟩)]
    ihave ⟨%Hsz, Hsuf, Hbback⟩ := suffix_acc buf0 n0 pend0 rest0 hn0 $$ Hbuf
    wp_auto
    wp_apply wp_slice_copy_Z (V := w8) (slice.slice buf0 w8 n0 buf0.len) rest0 pc (ps.drop j) dq
      $$ [$Hsuf $Hpc] as %m ⟨%Hm, Hsuf, Hpc⟩
    have hdrop : rest0.drop (ps.drop j).length = [] := List.drop_eq_nil_of_le (by omega)
    rw [hdrop, List.append_nil]
    have hmr : sint.Z m = rest0.length := by rw [Hm, Nat.min_eq_left (by omega)]
    ihave Hbuf := Hbback $$ %_ %(by simp; omega) Hsuf
    isimp at Hb
    have hXl : ((ps.drop j).take rest0.length).length = rest0.length := by simp; omega
    have hX : sent0 ++ (pend0 ++ (ps.drop j).take rest0.length) =
        sent ++ pend ++ ps.take (j + rest0.length) := by
      rw [← List.append_assoc, hsent, List.take_add, List.append_assoc]
    ihave #HQ1 := Q_of_prefix Q (sent0 ++ (pend0 ++ (ps.drop j).take rest0.length))
      (sent ++ pend ++ ps)
      (by rw [hX]; exact (List.prefix_append_right_inj _).mpr (List.take_prefix _ _))
      $$ HQpc HQall
    wp_apply wp_Flush bw (interface.ok e) J Q sent0 (pend0 ++ (ps.drop j).take rest0.length)
      interface.nil $$ [$Hpkg $Hwr HJ Hb Hbuf] as %e1 ⟨%k1, %Hk1, Hown⟩
    · iunfold ownWriter, writerRep
      iframe HJ HQ1
      iexists buf0, _, []
      rw [List.append_nil]
      iframe Hb Hbuf Herr0
      ipureintro
      constructor
      · simp only [List.length_append, hXl]; word
      · simp; omega
    have hmW : m = W64 rest0.length := by
      apply BitVec.eq_of_toInt_eq
      show sint.Z m = sint.Z (W64 rest0.length)
      rw [hmr, sint_Z_W64_length (by omega)]
    subst hmW
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
    ihave ⟨-, Hpc, Hpback⟩ := slice_advance pc dq ps j rest0.length (by omega) _ $$ [$Hpc $Hpback]
    wp_auto
    wp_for_post
    iunfold ownWriter, writerRep at Hown
    icases Hown with ⟨HJ, -, %buf', %n', %rest', Hb, Hbuf, %Hn', #Herr'⟩
    iframe
    iexists j + rest0.length, _, _, sent0 ++ (pend0 ++ (ps.drop j).take rest0.length).take k1,
      (pend0 ++ (ps.drop j).take rest0.length).drop k1, rest', buf', n', e1
    iframe Hpc Hpback HJ Hb Hbuf Herr' nn p
    ipureintro
    refine ⟨by word, by omega, Hn'.1, Hn'.2, ?_, hpre.trans (List.prefix_append _ _),
      fun h => absurd (herr h).1.symm h⟩
    rw [List.append_assoc, List.take_append_drop, hX]
  -- it fits
  (try simp only [goose_wp_simp_extra, Bool.false_eq_true, ↓reduceIte])
  (try wp_for_post)
  rcases err0 with ei | _
  · write_err_tail
  have hfits : ps.length - j ≤ rest0.length := by omega
  have hdl : (ps.drop j).length = ps.length - j := List.length_drop
  wp_auto
  ihave %Hbwf := ownSlice_wf _ _ _ $$ Hbuf
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, Hbwf.2⟩)]
  ihave ⟨%Hsz, Hsuf, Hbback⟩ := suffix_acc buf0 n0 pend0 rest0 hn0 $$ Hbuf
  wp_auto
  wp_apply wp_slice_copy_Z (V := w8) (slice.slice buf0 w8 n0 buf0.len) rest0 pc (ps.drop j) dq
    $$ [$Hsuf $Hpc] as %m ⟨%Hm, Hsuf, Hpc⟩
  have hmr : sint.Z m = ps.length - j := by
    rw [Hm, Nat.min_eq_right (by omega), hdl]; omega
  have htk : (ps.drop j).take rest0.length = ps.drop j := List.take_of_length_le (by omega)
  rw [htk]
  ihave Hbuf := Hbback $$ %_ %(by simp; omega) Hsuf
  (try wp_auto)
  isimp at Hb
  ihave Hp := Hpback $$ Hpc
  have hfin : sent0 ++ (pend0 ++ ps.drop j) = sent ++ pend ++ ps := by
    rw [← List.append_assoc, hsent, List.append_assoc (sent ++ pend), List.take_append_drop]
  ihave #HQf := Q_of_prefix Q (sent0 ++ (pend0 ++ ps.drop j)) (sent ++ pend ++ ps)
    (by rw [hfin]; exact List.prefix_refl _) $$ HQpc HQall
  iapply HΦ
  iexists ps.length, sent0, pend0 ++ ps.drop j
  iframe Hp
  isplitr
  · ipureintro
    refine ⟨?_, Nat.le_refl _, by rw [List.take_length, ← hfin], hpre,
      fun _ => rfl, fun h => absurd (herr h).1.symm h⟩
    apply BitVec.eq_of_toInt_eq
    show sint.Z (nnv + m) = sint.Z (W64 ps.length)
    rw [sint_Z_W64_length (by omega)]
    word
  iunfold ownWriter, writerRep
  iframe HJ HQf
  iexists buf0, _, rest0.drop (ps.drop j).length
  rw [List.append_assoc pend0]
  iframe Hb Hbuf Herr0
  ipureintro
  constructor
  · simp only [List.length_append, hdl]; word
  · simp only [List.length_append, List.length_drop] at hlen0 ⊢; omega

end proofs

end bufio

end Perennial
