/- Lean-first (no Rocq counterpart). The proof of `db.close()`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__close
public import Spec.os.File__Fd
public import Spec.os.File__Close
public import Spec.syscall.Flock

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

theorem DB.close.wp_proof (wp_munmap : DB.munmap.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Flock : syscall.Flock.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG)) :
    DB.close.spec (GF := GF) (hG := hG) := by
  intro db sl dsz m0 m1 f dqd fd name d
  wp_start as ⟨#Hinv, Hd, Hs, H0, H1, Hm, Hfile, Hf, Hfd⟩
  (try wp_auto)
  wp_apply wp_munmap db sl dsz m0 m1 $$ [Hd Hs H0 H1 Hm] as %err ⟨Hd, Hflds, Hun⟩
  · iframe
  (try wp_auto)
  wp_apply wp_Fd f fd name _ $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  wp_apply wp_Flock fd _ _ d $$ [Hinv Hfd] as %e Hfd
  · iframe; iframe #
  (try wp_auto)
  wp_apply wp_Close f fd name d $$ [Hinv Hf Hfd] as %err2 Hf
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  iframe
