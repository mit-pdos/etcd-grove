/-
**`poll.CopyFileRange`'s loop in `io.CopyFiles.spec`'s copy** (`os.modelPollCopyFileRange`, the Go
model): rounds of `copy_file_range` (`os.wp_cfrRound`) from the source's offset `o + j`
to the destination's `j`, `EINTR` retried, each judged by `modelHandleCopyFileRangeErr` (poll's, copied). Every
round keeps the copy's state `io.cpG` (the destination the source's bytes `[o, o + j)`, both offsets at
their ends), so the loop ends in it, at some `j'`; handled with no error only at the source's end.
Lean-first.
-/
module

public import Proof.io.CopyRound
public import Proof.os.ForLoeb
public import Proof.os.ErrorOk

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

/-- `modelHandleCopyFileRangeErr(modelErrno(e), copied, written)` (poll's `handleCopyFileRangeErr`):
`err` is `nil` or the errno's error; handled with no error only when `e = 0`, and so when `e = 0` and
something was copied. -/
theorem os.wp_modelHandleCFRErr (e copied written : w64) :
    {{ (True : IProp GF) }}
      (App (App (App (Val (@! os.modelHandleCopyFileRangeErr)) (Val #(errnoErr e))) (Val #copied))
        (Val #written))
    {{ (h : Bool) (err : GoInterface), RET (PairV #h #err);
        ⌜(err = interface.nil ∨ err = errnoErr e) ∧ (h = true → err = interface.nil → e = W64 0) ∧
          (e = W64 0 → copied ≠ W64 0 → h = true ∧ err = interface.nil)⌝ }} := by
  wp_start as -
  by_cases he0 : e = W64 0
  · subst he0
    rw [show errnoErr (W64 0) = interface.nil by unfold errnoErr; exact if_pos rfl]
    try wp_auto
    by_cases hc : copied = W64 0
    · rw [decide_eq_true hc]
      try wp_auto
      by_cases hw : written = W64 0
      · rw [decide_eq_true hw]
        try wp_auto
        iapply HΦ
        ipureintro
        exact ⟨Or.inl rfl, (fun h => by cases h), fun _ h => absurd hc h⟩
      · rw [decide_eq_false hw]
        try wp_auto
        iapply HΦ
        ipureintro
        exact ⟨Or.inl rfl, fun _ _ => rfl, fun _ h => absurd hc h⟩
    · rw [decide_eq_false hc]
      try wp_auto
      iapply HΦ
      ipureintro
      exact ⟨Or.inl rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  · have hE : errnoErr e = interface.mkOk syscall.Errno.ty #e := by unfold errnoErr; exact if_neg he0
    rw [hE]
    try rw [errno_ty_eq]
    try wp_auto
    try rw [errno_ty_eq]
    by_cases hX38 : e = W64 38
    · subst hX38
      try wp_auto
      iapply HΦ
      ipureintro
      exact ⟨Or.inl rfl, (fun h => by cases h), fun h => absurd h he0⟩
    rw [decide_eq_false hX38]
    try wp_auto
    by_cases hX1 : e = W64 1
    · subst hX1
      try wp_auto
      iapply HΦ
      ipureintro
      exact ⟨Or.inl rfl, (fun h => by cases h), fun h => absurd h he0⟩
    rw [decide_eq_false hX1]
    try wp_auto
    by_cases hX95 : e = W64 95
    · subst hX95
      try wp_auto
      iapply HΦ
      ipureintro
      exact ⟨Or.inl rfl, (fun h => by cases h), fun h => absurd h he0⟩
    rw [decide_eq_false hX95]
    try wp_auto
    by_cases hX5 : e = W64 5
    · subst hX5
      try wp_auto
      iapply HΦ
      ipureintro
      exact ⟨Or.inl rfl, (fun h => by cases h), fun h => absurd h he0⟩
    rw [decide_eq_false hX5]
    try wp_auto
    by_cases hX22 : e = W64 22
    · subst hX22
      try wp_auto
      iapply HΦ
      ipureintro
      exact ⟨Or.inl rfl, (fun h => by cases h), fun h => absurd h he0⟩
    rw [decide_eq_false hX22]
    try wp_auto
    by_cases hX18 : e = W64 18
    · subst hX18
      try wp_auto
      iapply HΦ
      ipureintro
      exact ⟨Or.inl rfl, (fun h => by cases h), fun h => absurd h he0⟩
    rw [decide_eq_false hX18]
    try wp_auto
    iapply HΦ
    ipureintro
    exact ⟨Or.inr rfl, (fun _ h => by cases h), fun h => absurd h he0⟩

theorem os.wp_pollCFR (ind ins : Loc) (fdd fds : w64) (dqd dqs dqfd dqfs : DFrac)
    (dd ds : OsFd) (m : OsMeta) (qm qb : DFrac) (bs : List ByteG) (o j : Nat)
    (hfdd : 0 ≤ fdd.toInt) (hfds : 0 ≤ fds.toInt) (hwr : dd.writable = true) (hrd : ds.readable = true)
    (hbs : bs.length = m.size) (hm : m.size < 2 ^ 61) :
    {{ osInv (GF := GF) ∗ structFieldRef internal.poll.FD go!"Sysfd" (structFieldRef os.file go!"pfd" ind) ↦{dqd} fdd ∗
        structFieldRef internal.poll.FD go!"Sysfd" (structFieldRef os.file go!"pfd" ins) ↦{dqs} fds ∗
        osFd fdd dqfd dd ∗ osFd fds dqfs ds ∗ osMeta ds.ino qm m ∗ osBytes ds.ino 0 qb bs ∗
        io.cpG ind ins dd.ino o bs j }}
      (App (App (App (Val (@! os.modelPollCopyFileRange)) (Val #ind)) (Val #ins))
        (Val #(W64 0x7fffffffffffffff)))
    {{ (wr : w64) (h : Bool) (err : GoInterface), RET (PairV (PairV #wr #h) #err);
        structFieldRef internal.poll.FD go!"Sysfd" (structFieldRef os.file go!"pfd" ind) ↦{dqd} fdd ∗ structFieldRef internal.poll.FD go!"Sysfd" (structFieldRef os.file go!"pfd" ins) ↦{dqs} fds ∗
        osFd fdd dqfd dd ∗ osFd fds dqfs ds ∗ osMeta ds.ino qm m ∗ osBytes ds.ino 0 qb bs ∗
        ∃ j' : Nat, io.cpG ind ins dd.ino o bs j' ∗ ⌜(h = true → err = interface.nil → o + j' = bs.length) ∧
          ∃ e : w64, err = errnoErr e⌝ }} := by
  wp_start as ⟨#Hinv, Hdfd, Hsfd, Hfdd, Hfds, Hm, Hbs, HG⟩
  try wp_auto
  ihave Hst : (∃ (rem0 wr0 : w64) (hd0 : Bool) (er0 : GoInterface), remain_ptr ↦ rem0 ∗
      written_ptr ↦ wr0 ∗ handled_ptr ↦ hd0 ∗ err_ptr ↦ er0 ∗
      ⌜2 ^ 63 - 1 ≤ sint.Z rem0 + j⌝ : IProp GF) $$ [remain written handled err]
  · iexists _, _, _, _
    iframe
    ipureintro
    have : sint.Z (W64 9223372036854775807) = 2 ^ 63 - 1 := rfl
    omega
  icases Hst with ⟨%rem0, %wr0, %hd0, %er0, Hrem, Hwr, Hhd, Her, %hrem⟩
  wp_for_bind
  iloeb as IH generalizing %rem0 %wr0 %hd0 %er0 %j %hrem Hrem Hwr Hhd Her HG HΦ Hdfd Hsfd Hfdd Hfds Hm Hbs src dst
  wp_for_step
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
  ihave Hnc : (∃ (n0 c0 : w64), n_ptr ↦ n0 ∗ c_ptr ↦ c0 : IProp GF) $$ [n c]
  · iexists _, _; iframe
  icases Hnc with ⟨%n0, %c0, Hn, Hc⟩
  wp_for_bind
  iloeb as IH2 generalizing %n0 %c0 Hn Hc Hdfd Hsfd Hfdd Hfds Hm Hbs HG HΦ Hrem Hwr Hhd Her src dst max
  wp_for_step
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
  try wp_auto
  by_cases he4 : e = W64 4
  · have hk0 : k = 0 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact h
      · have := hk1 h; rw [this] at he4; exact absurd he4 (by decide)
    subst hk0
    try rw [decide_eq_true he4]
    try wp_auto
    wp_for_post
    inext
    iapply IH2 $$ %_ %_ Hn Hc Hdfd Hsfd Hfdd Hfds Hm Hbs HG HΦ Hrem Hwr Hhd Her src dst max
  try rw [decide_eq_false he4]
  try wp_auto
  wp_for_post
  have hkZ : sint.Z (W64 (k : Int)) = k := (os.cfr_natZ k (by omega)).1
  by_cases hkp : 0 < k
  · rw [decide_eq_true (show sint.Z (W64 0) < sint.Z (W64 (k : Int)) by rw [hkZ, show sint.Z (W64 0) = 0 from rfl]; omega)]
    try wp_auto
    have he0 := hk1 hkp
    subst he0
    have hkne : ¬ (W64 (k : Int)) = W64 0 := by
      intro h; have := congrArg BitVec.toNat h; simp at this; omega
    wp_apply os.wp_modelErrno
    wp_apply os.wp_modelHandleCFRErr as %hd %er %hh
    obtain ⟨rfl, rfl⟩ := hh.2.2 rfl hkne
    try wp_auto
    try rw [decide_eq_false hkne]
    try wp_auto
    have hremk : sint.Z (rem0 - W64 (k : Int)) = sint.Z rem0 - k := by
      have h1 : sint.Z rem0 < 2 ^ 63 := by simp only [sint.Z]; word
      simp only [sint.Z] at hkZ hrem h1 ⊢; word
    wp_for_post
    inext
    iapply IH $$ %(rem0 - W64 (k : Int)) %(wr0 + W64 (k : Int)) %true %interface.nil %(j + k)
      %(by rw [hremk]; push_cast; omega) Hrem Hwr Hhd Her HG HΦ Hdfd Hsfd Hfdd Hfds Hm Hbs src dst
  · have hk0 : k = 0 := by omega
    subst hk0
    rw [decide_eq_false (show ¬ sint.Z (W64 0) < sint.Z (W64 ((0 : Nat) : Int)) by decide)]
    try wp_auto
    wp_apply os.wp_modelErrno
    wp_apply os.wp_modelHandleCFRErr as %hd %er %hh
    try wp_auto
    try rw [decide_eq_true (show W64 ((0 : Nat) : Int) = W64 0 from rfl)]
    try wp_auto
    wp_for_post
    iapply HΦ
    iframe
    ipureintro
    obtain ⟨her, hhe, -⟩ := hh
    refine ⟨fun h1 h2 => ?_, ?_⟩
    · have he := hhe h1 h2
      have := hk2 rfl he
      omega
    · rcases her with rfl | rfl
      · exact ⟨W64 0, by unfold errnoErr; exact (if_pos rfl).symm⟩
      · exact ⟨e, rfl⟩

end proof

end EtcdGrove
end Perennial
