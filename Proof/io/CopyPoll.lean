/-
**`poll.CopyFileRange`'s loop in `io.CopyFiles.spec`'s copy** (`model.pollCopyFileRange`,
`TrustedCode/os.lean`): rounds of `copy_file_range` (`os.wp_cfrRound`) from the source's offset `o + j`
to the destination's `j`, `EINTR` retried, each judged by `handleCopyFileRangeErr` (translated). Every
round keeps the copy's state `io.cpG` (the destination the source's bytes `[o, o + j)`, both offsets at
their ends), so the loop ends in it, at some `j'`; handled with no error only at the source's end.
Lean-first.
-/
module

public import Proof.io.CopyRound

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem io.cpG_vals (bs : List ByteG) (o j k : Nat) :
    ((bs.map Prod.fst).drop o).take j ++ ((bs.map Prod.fst).drop (W64 (o + j)).toNat).take k =
      ((bs.map Prod.fst).drop o).take (j + k) ∨ 2 ^ 64 ≤ o + j := by
  by_cases h : o + j < 2 ^ 64
  · left
    rw [show (W64 (o + j)).toNat = o + j by simp; omega, List.take_add, List.drop_drop]
  · right; omega

/-- **The copy's state at `j`**: the destination holds the source's bytes `[o, o + j)`, its offset
`j`, the source's `o + j`. -/
def io.cpG (ind ins : Loc) (i : Ino) (o : Nat) (bs : List ByteG) (j : Nat) : IProp GF :=
  iprop(⌜o + j ≤ bs.length⌝ ∗ structFieldRef os.file go!"off" ind ↦ W64 j ∗
    structFieldRef os.file go!"off" ins ↦ W64 (o + j) ∗
    io.copyDst i (· = ((bs.map Prod.fst).drop o).take j))

/-- Names the two arguments of a call `f a b` (to generalize them before a Löb induction). -/
theorem os.wp_genArgs2 (f : val) (a b : w64) (Φ : val → IProp GF) :
    (∀ a' : w64, ∀ b' : w64, ⌜a' = a⌝ -∗ ⌜b' = b⌝ -∗ WP (App (App (Val f) (Val #a')) (Val #b')) {{ Φ }}) ⊢
      WP (App (App (Val f) (Val #a)) (Val #b)) {{ Φ }} := by
  iintro H
  iapply H <;> ipureintro <;> rfl

-- The `k = 0` exit of `os.wp_pollCFR` with an unhandled result `(false, nil)`.
local macro "cfr_unhandled" hΦ:pmTerm : tactic => `(tactic| (
  try wp_auto
  rw [show (go!"os.wrapSyscallError" : GoString) = _root_.Perennial.os.wrapSyscallError from rfl]
  wp_func_call
  wp_call
  try wp_auto
  iapply $hΦ
  iframe
  ipureintro
  exact ⟨fun h => (by cases h), Or.inl rfl⟩))

theorem os.wp_pollCFR (ind ins : Loc) (fdd fds : w64) (dqd dqs dqfd dqfs : DFrac)
    (dd ds : OsFd) (m : OsMeta) (qm qb : DFrac) (bs : List ByteG) (o j : Nat)
    (hfdd : 0 ≤ fdd.toInt) (hfds : 0 ≤ fds.toInt) (hwr : dd.writable = true) (hrd : ds.readable = true)
    (hbs : bs.length = m.size) (hm : m.size < 2 ^ 61) :
    {{ osInv (GF := GF) ∗ structFieldRef os.file go!"fd" ind ↦{dqd} fdd ∗
        structFieldRef os.file go!"fd" ins ↦{dqs} fds ∗
        osFd fdd dqfd dd ∗ osFd fds dqfs ds ∗ osMeta ds.ino qm m ∗ osBytes ds.ino 0 qb bs ∗
        io.cpG ind ins dd.ino o bs j }}
      (App (App (App (App (Val (@! os.modelPollCopyFileRange)) (Val #ind)) (Val #ins))
        (Val #(null : Loc))) (Val #(W64 0x7fffffffffffffff)))
    {{ (wr : w64) (h : Bool) (err : GoInterface), RET (PairV (PairV #wr #h) #err);
        structFieldRef os.file go!"fd" ind ↦{dqd} fdd ∗ structFieldRef os.file go!"fd" ins ↦{dqs} fds ∗
        osFd fdd dqfd dd ∗ osFd fds dqfs ds ∗ osMeta ds.ino qm m ∗ osBytes ds.ino 0 qb bs ∗
        ∃ j' : Nat, io.cpG ind ins dd.ino o bs j' ∗ ⌜(h = true → err = interface.nil → o + j' = bs.length) ∧
          (err = interface.nil ∨ ∃ l : Loc, err = interface.mkOk (go.GoType.PointerType os.SyscallError.ty) #l)⌝ }} := by
  iintro %Φ ⟨#Hinv, Hdfd, Hsfd, Hfdd, Hfds, Hm, Hbs, HG⟩ HΦ
  unfold os.model.pollCopyFileRange
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_pure
  wp_bind (App (App (Val _) (Val _)) (Val _))
  iapply os.wp_genArgs2
  iintro %rem0 %wr0 %hrem0 %hwr0
  have hrem : 2 ^ 63 - 1 ≤ sint.Z rem0 + j := by rw [hrem0]; have : sint.Z (W64 9223372036854775807) = 2 ^ 63 - 1 := rfl; omega
  clear hrem0 hwr0
  iloeb as IH generalizing %rem0 %wr0 %j %hrem HG HΦ
  try wp_auto
  iunfold io.cpG at HG
  icases HG with ⟨%hj0, HG⟩
  ihave HG : io.cpG ind ins dd.ino o bs j $$ [HG]
  · iunfold io.cpG; iframe; ipureintro; exact hj0
  rw [decide_eq_false (show ¬ sint.Z rem0 ≤ sint.Z (W64 0) by
    rw [show sint.Z (W64 0) = 0 from rfl]; omega)]
  try wp_auto
  rw [decide_eq_false (show ¬ sint.Z rem0 < sint.Z (W64 2147479552) by
    rw [show sint.Z (W64 2147479552) = 2147479552 from rfl]; omega)]
  try wp_auto
  iloeb as IH2 generalizing Hdfd Hsfd Hfdd Hfds Hm Hbs HG HΦ
  iunfold io.cpG at HG
  icases HG with ⟨%hj, Hdoff, Hsoff, Hdst⟩
  have hvl : (((bs.map Prod.fst).drop o).take j).length = j := by
    simp only [List.length_take, List.length_drop, List.length_map]; omega
  wp_apply (os.wp_cfrRound ind ins fdd fds (W64 j) (W64 (o + j)) (W64 2147479552) dqd dqs dqfd dqfs dd ds m
    qm qb bs (((bs.map Prod.fst).drop o).take j) hfdd hfds hwr hrd (by rw [hvl])
    (by have := os.cfr_natInt (o + j) (by omega); push_cast at this; omega)
    (by have := (os.cfr_natZ (o + j) (by omega)).2; push_cast at this; omega) hbs hm (by omega) (by decide) (by decide))
    $$ [Hdfd Hdoff Hsfd Hsoff Hfdd Hfds Hm Hbs Hdst]
    as %w %e ⟨Hdfd, Hsfd, Hfdd, Hfds, Hm, Hbs, %k, %hk, Hdoff, Hsoff, Hdst⟩
  · iframe; iexact Hinv
  obtain ⟨rfl, hkmx, hk1, hk2, hk3⟩ := hk
  have hoj := (os.cfr_natZ (o + j) (by omega)).2
  push_cast at hoj
  rw [hoj] at hk2 hk3
  rw [os.cfr_W64_addI, os.cfr_W64_addI]
  rcases io.cpG_vals bs o j k with hv | hv
  rotate_left
  · omega
  rw [hv]
  ihave HG : io.cpG ind ins dd.ino o bs (j + k) $$ [Hdoff Hsoff Hdst]
  · iunfold io.cpG
    push_cast
    rw [show ((o : Int) + (j + k)) = o + j + k by omega]
    iframe
    ipureintro; omega
  by_cases he4 : e = W64 4
  · have hk0 : k = 0 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact h
      · have := hk1 h; rw [this] at he4; exact absurd he4 (by decide)
    subst hk0
    rw [decide_eq_true he4]
    wp_pure
    wp_pure
    iapply IH2 $$ Hdfd Hsfd Hfdd Hfds Hm Hbs HG HΦ
  rw [decide_eq_false he4]
  try wp_auto
  have hkZ : sint.Z (W64 (k : Int)) = k := (os.cfr_natZ k (by omega)).1
  by_cases hkp : 0 < k
  · rw [decide_eq_true (show sint.Z (W64 0) < sint.Z (W64 (k : Int)) by rw [hkZ, show sint.Z (W64 0) = 0 from rfl]; omega)]
    try wp_auto
    have he0 := hk1 hkp
    subst he0
    rw [decide_eq_true (show sint.Z (W64 0) < sint.Z (W64 (k : Int)) by rw [hkZ, show sint.Z (W64 0) = 0 from rfl]; omega)]
    try wp_auto
    unfold syscall.model.errno
    try wp_auto
    rw [show (go!"internal/poll.handleCopyFileRangeErr" : GoString) =
      _root_.Perennial.internal.poll.handleCopyFileRangeErr from rfl]
    wp_func_call
    wp_call
    try wp_auto
    have hkne : ¬ (W64 (k : Int)) = W64 0 := by
      intro h; have := congrArg BitVec.toNat h; simp at this; omega
    rw [decide_eq_false hkne]
    try wp_auto
    rw [decide_eq_false hkne]
    have hremk : sint.Z (rem0 - W64 (k : Int)) = sint.Z rem0 - k := by
      have h1 : sint.Z rem0 < 2 ^ 63 := by simp only [sint.Z]; word
      simp only [sint.Z] at hkZ hrem h1 ⊢; word
    repeat (first
      | iapply IH $$ %(rem0 - W64 (k : Int)) %(wr0 + W64 (k : Int)) %(j + k) %(by rw [hremk]; push_cast; omega) HG HΦ
           Hdfd Hsfd Hfdd Hfds Hm Hbs
      | wp_pure)
  · have hk0 : k = 0 := by omega
    subst hk0
    rw [decide_eq_false (show ¬ sint.Z (W64 0) < sint.Z (W64 ((0 : Nat) : Int)) by decide)]
    try wp_auto
    unfold syscall.model.errno
    try wp_auto
    by_cases he0 : e = W64 0
    · subst he0
      rw [decide_eq_true (rfl : W64 0 = W64 0)]
      try wp_auto
      rw [show (go!"internal/poll.handleCopyFileRangeErr" : GoString) =
        _root_.Perennial.internal.poll.handleCopyFileRangeErr from rfl]
      wp_func_call
      wp_call
      try wp_auto
      by_cases hw : wr0 = W64 0
      · rw [decide_eq_true hw]
        try wp_auto
        rw [show (go!"os.wrapSyscallError" : GoString) = _root_.Perennial.os.wrapSyscallError from rfl]
        wp_func_call
        wp_call
        try wp_auto
        iapply HΦ
        iframe
        ipureintro
        exact ⟨fun h => (by cases h), Or.inl rfl⟩
      · rw [decide_eq_false hw]
        try wp_auto
        rw [show (go!"os.wrapSyscallError" : GoString) = _root_.Perennial.os.wrapSyscallError from rfl]
        wp_func_call
        wp_call
        try wp_auto
        iapply HΦ
        iframe
        ipureintro
        refine ⟨fun _ _ => ?_, Or.inl rfl⟩
        have := hk2 rfl rfl
        omega
    · rw [decide_eq_false he0, errno_ty_eq]
      try wp_auto
      rw [show (go!"internal/poll.handleCopyFileRangeErr" : GoString) =
        _root_.Perennial.internal.poll.handleCopyFileRangeErr from rfl]
      wp_func_call
      wp_call
      try wp_auto
      by_cases hX38 : e = W64 38
      · subst hX38
        cfr_unhandled HΦ
      rw [decide_eq_false hX38]
      try wp_auto
      by_cases hX1 : e = W64 1
      · subst hX1
        cfr_unhandled HΦ
      rw [decide_eq_false hX1]
      try wp_auto
      by_cases hX95 : e = W64 95
      · subst hX95
        cfr_unhandled HΦ
      rw [decide_eq_false hX95]
      try wp_auto
      by_cases hX5 : e = W64 5
      · subst hX5
        cfr_unhandled HΦ
      rw [decide_eq_false hX5]
      try wp_auto
      by_cases hX22 : e = W64 22
      · subst hX22
        cfr_unhandled HΦ
      rw [decide_eq_false hX22]
      try wp_auto
      by_cases hX18 : e = W64 18
      · subst hX18
        cfr_unhandled HΦ
      rw [decide_eq_false hX18]
      try wp_auto
      rw [show (go!"os.wrapSyscallError" : GoString) = _root_.Perennial.os.wrapSyscallError from rfl]
      wp_func_call
      wp_call
      try wp_auto
      wp_func_call
      wp_call
      try wp_auto
      wp_alloc l as Hl
      try wp_auto
      iapply HΦ
      iframe
      ipureintro
      exact ⟨fun _ h => (by cases h), Or.inr ⟨l, rfl⟩⟩

end proof

end EtcdGrove
end Perennial
