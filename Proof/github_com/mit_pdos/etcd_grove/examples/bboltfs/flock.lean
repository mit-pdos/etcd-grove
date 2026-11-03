/- Lean-first (no Rocq counterpart). The proof of `flock(f, exclusive)`: a loop whose invariant is the file and its fd. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.flock
public import Spec.os.File__Fd
public import Spec.syscall.Flock
public import Perennial.Spec.time.Sleep

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

theorem flock.wp_proof (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Flock : syscall.Flock.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG)) :
    flock.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d exclusive
  wp_start as ⟨#Hinv, Hf, Hfd⟩
  wp_auto
  wp_apply wp_Fd f fd name dqf $$ [Hf] as Hf
  · iexact Hf
  ihave IH : iprop(True) $$ []
  · itrivial
  cases exclusive <;> wp_auto <;>
  ( wp_for IH
    wp_apply wp_Flock fd _ dq d $$ [Hinv Hfd] as %e Hfd
    · iframe; iframe #
    by_cases he : e = 0
    · subst he; unfold errnoErr; rw [if_pos rfl]
      wp_auto
      wp_for_post
      iapply HΦ; iframe
    · unfold errnoErr; rw [if_neg he]
      wp_auto
      wp_if_destruct <;> (try wp_auto) <;>
        first
        | (wp_for_post; iapply HΦ; iframe; done)
        | (wp_apply wp_Sleep; wp_for_post; iframe))

end proof

end bboltfs
end EtcdGrove
end Perennial
