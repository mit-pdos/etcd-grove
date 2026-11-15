/- Lean-first (no Rocq counterpart). The proof of `db.close()`. -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__close
public import LinuxFs.Spec.os.File__Fd
public import LinuxFs.Spec.os.File__Close
public import LinuxFs.Spec.syscall.Flock

@[expose] public section

noncomputable section

namespace Perennial

open Fs
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

theorem DB.close.wp_proof (wp_munmap : DB.munmap.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Flock : syscall.Flock.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG)) :
    DB.close.spec (GF := GF) (hG := hG) := by
  intro db dq sl dsz m0 m1 f dqd fd name d p m Hdq
  wp_start as ⟨#Hinv, Hd, Hs, H0, H1, Hm, Hfile, Hf, Hfd, Hlt⟩
  iunfold lockToks at Hlt
  icases Hlt with ⟨Hlo, Hfl⟩
  (try wp_auto)
  wp_apply wp_munmap db dq sl dsz m0 m1 p m Hdq $$ [Hd Hs H0 H1 Hm] as %err ⟨Hd, Hs, H0, H1, Hun⟩
  · iframe
  (try wp_auto)
  wp_apply wp_Fd f fd name _ $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  wp_apply wp_Flock fd (W64 8) d none false rfl (fun h => absurd rfl h) $$ [Hinv Hfd Hfl] as %e Hout
  · iframe; iframe #
  (try wp_auto)
  unfold lockOut
  icases Hout with ⟨%d', Hfd, Hfl, %hd'⟩
  ihave Hlo : lockTok LockKind.ofd fd d' $$ [Hlo]
  · rcases hd'.1 with rfl | rfl
    · iexact Hlo
    · iapply (lockTok_setLk_ne fd d none (by decide)).2; iexact Hlo
  wp_apply wp_Close f fd name d' $$ [Hinv Hf Hfd Hlo Hfl] as %err2 ⟨Hf, -⟩
  · unfold lockToks; iframe; iframe #
  cases err with
  | nil =>
    (try wp_auto)
    iapply HΦ
    iframe
    ipureintro; intro _; rfl
  | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe
    ipureintro; intro h; exact h
