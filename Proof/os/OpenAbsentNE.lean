/-
`open(2)` without `O_CREAT` of `d/b`, a name holding nothing, with its errno witnessed when the file
system does not fail on `d/b` (`FsNoErrAt`, `NoErrRemoveSteps.lean`), through `wp_fs_postSh` (claim #34,
2026-11-23): `ENOENT` from a state with a free fd (`NoIoErr`'s `PathErrno`, its `open` case, the user's
approval of 2026-11-23), `EINTR` from one with none (`NoMapLockErr`), which every model of `open`
retries (`openAbsent_noErrAt`, `wp_osOpenAbsentSW`); so `os.OpenFile`/`os.Open` of it return a
`*PathError` of `ENOENT` (`os.OpenFile.wp_absentErrSW`, `os.Open.wp_absentErrSW`). What `wal.Exist`'s
`ReadDir` of an absent WAL directory needs to answer `false`. Untrusted.
-/
module

public import Proof.os.RemoveAllNE
public import Proof.os.NsChildS

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section step
variable [GooseExts] [GoGlobalContext] [go.BasicIntoValInj] [S : ExtSemantics fsExt] [FsSemOk]

/-- **`open(2)` without `O_CREAT` of a covered `d/b` holding nothing**, `d` a directory: a failure is
`ENOENT`, or `EINTR` with no free fd. -/
theorem openAbsent_noErrAt {d b : GoString} {j : Ino} {k : Nat} {fl : w64} (hne : FsNoErrAt (child d b))
    (hcr : fl.toNat / O_CREAT % 2 = 0)
    {h : GMap Loc (NonAtomic val)} {st : OsState} {g : Unit} {e' : Expr}
    {h' : GMap Loc (NonAtomic val)} {st' : OsState} {g' : Unit}
    (hd : st.lookup d = some (.dir j)) (hb : NameOk b) (hlk : st.lookup (child d b) = none)
    (hs : S.step "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) h st g e' h' st' g') :
    ∀ fd e : w64, e' = osRes (#fd) e → e ≠ 0 → e = ENOENT ∨ e = EINTR := by
  obtain ⟨⟨Sio, -, h1, h2, hp⟩, hfit⟩ := hne
  have hst := (fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)).1
  have hcr' : decide ((fl.toNat / O_CREAT) % 2 = 1) = false := by simp [hcr]
  intro fd e he he0
  by_cases hf : ∃ fd', FdFree st fd'
  · left
    have hcov : IoCovers Sio "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) st :=
      ⟨k, child d b, fl, rfl, hp _ rfl, hfit⟩
    have hno : ¬ ∃ e'' st'', IsFsStep "Open" (PairV (osTokV k) (PairV (#(child d b)) (#fl))) st e'' st'' ∧
        ErrnoZero "Open" e'' := by
      rintro ⟨e'', st'', hs'', r, rfl⟩
      simp only [IsFsStep] at hs''
      rcases hs'' with ⟨p1, fl1, t1, s1, hv1, -, -, -, -, hr⟩ | ⟨p1, fl1, t1, s1, hv1, hn1, -⟩
      · obtain ⟨-, hp1, hf1⟩ := tokPathFl_inj hv1
        subst hp1 hf1
        have hl0 : (st.metaEnd t1).lookup (child d b) = none := hlk
        rcases hr with ⟨st1, tgt, fd1, hoe, -⟩ | ⟨e2, he2, -, hr2, -⟩
        · simp only [OpenEffect, hl0, hcr', Bool.false_eq_true, _root_.false_and] at hoe
        · injection hr2 with hr2
          injection hr2 with _ hr2
          exact he2 (go.intoVal_inj hr2).symm
      · obtain ⟨-, hp1, -⟩ := tokPathFl_inj hv1
        subst hp1
        exact hn1 (.inr (treeName_child hd hb))
    obtain ⟨k3, p3, fl3, hv3, hpe⟩ := noIoErr_pathErrno (Sio := Sio) hs hcov hno
    obtain ⟨rfl, rfl, rfl⟩ := tokPathFl_inj hv3
    have := hpe ⟨hcr, hlk, ⟨_, parent_child hd hb⟩, hf⟩
    rw [he] at this
    injection this with this
    injection this with _ this
    exact go.intoVal_inj this
  · right
    exact open_failure_eintr (Sio := Sio) ⟨hp _ rfl, hfit⟩ (fun fd' h => absurd ⟨fd', h⟩ hf) hst hs
      fd e he he0

end step

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **`open(2)` without `O_CREAT` of `d/b`, a name holding nothing**, `wp_osOpenAbsentS` with its
errno witnessed: `ENOENT` or `EINTR` when the file system does not fail on `d/b`. -/
theorem wp_osOpenAbsentSW (R : Roots) (d b : GoString) (j : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (k s0 : Nat) (q : Qp) (fl : w64) (hfl : OpenFlagsOk fl.toNat)
    (hcr : fl.toNat / O_CREAT % 2 = 0) (htr : fl.toNat / O_TRUNC % 2 = 0) (hb : NameOk b)
    (hN : N.Mem b) (hi : h.cur !! b = none) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 (child d b) q -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ ⌜FsNoErrAt (child d b) → e = ENOENT ∨ e = EINTR⌝ -∗
        osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗
        osNames (L := L) j N dqn h -∗ Φ (PairV (#(-1 : w64)) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#fl)))))
        @ s; E {{ Φ }} := by
  iintro #Hinv #Hsi Hp Hn Hk HΦ
  iapply wp_fs_postSh "Open" _ (by simp [val.isPanic]) R
    iprop(osPathS (L := L) R d dq j ∗ osNames (L := L) j N dqn h)
    (fun st => PathNames st d j N h)
    (fun st Γn hR hcoh => pathNames_of R d dq j _ dqn h st Γn hR hcoh)
    (fun w => FsNoErrAt (child d b) → ∀ fd e : w64, w = PairV (#fd) (#e) → e ≠ 0 →
      e = ENOENT ∨ e = EINTR)
    (fun _ st _ e' _ _ _ hP hw _ hst => by
      obtain ⟨fd, e, he⟩ := open_isVal hst
      refine ⟨_, he, fun hne fd' e2 hw' he2 => ?_⟩
      have h2 : e2 = e := by injection hw' with _ hw'; exact (go.intoVal_inj hw').symm
      subst h2
      exact openAbsent_noErrAt hne hcr hP.1 hb (by rw [pathNames_child hw hP hb hN]; exact hi) hst
        fd e2 he he2)
    hE' Φ $$ Hsi [Hp Hn]
  · iframe
  iintro ⟨Hp, Hn⟩
  iapply wp_osOpenAbsentS R d b j N dq dqn h k s0 q fl hfl hcr htr hb hN hi hE hE' _
    $$ Hinv Hsi Hp Hn Hk
  iintro %e %he Hperm Hp Hn %hw
  iapply HΦ $$ %e %he [] Hperm Hp Hn
  ipureintro; exact fun hne => hw hne _ e rfl he

end specs

end Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

namespace EtcdGrove

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj]

/-- `os.OpenFile(d/b, flag, perm)`, `flag` without `O_CREAT` and `O_TRUNC`, of a name holding
nothing: a `*PathError` of a nonzero errno, `ENOENT` when the file system does not fail on `d/b`
(`OpenFile.wp_absentErrS` with the errno witnessed; the model retries `EINTR`). -/
theorem os.OpenFile.wp_absentErrSW (d b : GoString) (flag : w64) (perm : w32) (R : Roots) (j : Ino)
    (N : NameSet) (dq dqn : DFrac) (h : NamesH) (qc : Qp)
    (hfl : OpenFlagsOk (flag ||| W64 0x80000).toNat)
    (hcr : (flag ||| W64 0x80000).toNat / O_CREAT % 2 = 0)
    (htr : (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 0) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = none) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #flag)) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osNames j N dqn h ∗
        osCallPerm (callKey R d) qc ∗
        ∃ e : w64, ⌜e ≠ 0 ∧ f = null ∧ (FsNoErrAt (child d b) → e = ENOENT)⌝ ∗
          os.errnoPathErr err e }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  generalize hfl' : flag ||| W64 0x80000 = fl at hfl hcr htr ⊢
  imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  iloeb as IH generalizing Hperm Hp Hn HΦ
  icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  wp_apply wp_osCallBeginS R _ qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [os.file_ty_eq, os.File_ty_eq, show flag ||| W64 524288 = fl from hfl']
  (try wp_auto)
  wp_apply +noauto wp_osOpenAbsentSW R d b j N dq dqn h t s0 qc fl hfl hcr htr hb hN hi
    CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk
    as %e %he0 %hw Hperm Hp Hn
  wp_auto
  rw [decide_eq_false (show e ≠ W64 0 from he0)]
  wp_auto
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    try rw [os.file_ty_eq]
    try rw [os.File_ty_eq]
    iapply IH $$ Hperm Hp Hn HΦ
  rw [decide_eq_false (show e ≠ W64 4 from he4)]
  wp_auto
  wp_apply os.wp_pathError_errno as %err #Herr
  iapply HΦ
  iframe
  iexists e
  iframe Herr
  ipureintro
  exact ⟨he0, rfl, fun hne => (hw hne).resolve_right (fun h4 => he4 (h4.trans (by decide)))⟩

/-- `os.Open(d/b)` of a name holding nothing: a `*PathError` of a nonzero errno, `ENOENT` when the
file system does not fail on `d/b`. -/
theorem os.Open.wp_absentErrSW (d b : GoString) (R : Roots) (j : Ino) (N : NameSet)
    (dq dqn : DFrac) (h : NamesH) (qc : Qp) (hb : NameOk b) (hN : N.Mem b)
    (hi : h.cur !! b = none) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm (callKey R d) qc }}
      (App (Val (@! os.Open)) (Val #(child d b)))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osNames j N dqn h ∗
        osCallPerm (callKey R d) qc ∗
        ∃ e : w64, ⌜e ≠ 0 ∧ f = null ∧ (FsNoErrAt (child d b) → e = ENOENT)⌝ ∗
          os.errnoPathErr err e }} := by
  wp_start as ⟨#Hinv, #Hsi, Hp, Hn, Hperm⟩
  wp_auto
  have e : W64 0 ||| W64 0x80000 = flRO := by decide
  wp_apply os.OpenFile.wp_absentErrSW d b (W64 0) (W32 0) R j N dq dqn h qc
    (by rw [e]; exact flRO_ok) (by rw [e]; decide) (by rw [e]; decide) hb hN hi
    $$ [Hinv Hsi Hp Hn Hperm] as %f %err Hr
  · iframe; isplitl [] <;> iassumption
  iapply HΦ
  iexact Hr

end proof

end EtcdGrove
end Perennial

end
