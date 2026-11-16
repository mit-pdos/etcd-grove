/- Lean-first (no Rocq counterpart). The proof of `flock(f, exclusive)`: a loop whose invariant is the file and its fd. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.flock
public import Spec.os.File__Fd
public import Spec.syscall.Flock
public import Perennial.Spec.time.Sleep

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

theorem flock.wp_proof (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Flock : syscall.Flock.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG)) :
    flock.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf d exclusive hfree
  wp_start as ⟨#Hinv, Hf, Hfd⟩
  wp_auto
  wp_apply wp_Fd f fd name dqf $$ [Hf] as Hf
  · iexact Hf
  ihave IH : iprop(True) $$ []
  · itrivial
  cases exclusive <;> wp_auto <;>
  ( wp_for IH
    ihave Ht := lockTok_none (GF := GF) .flock fd d (by simp [OsFd.lk, hfree])
    first
    | wp_apply wp_Flock fd (W64 4 ||| W64 2) d (some true) true (by rfl) (fun _ => hfree)
        $$ [Hinv Hfd Ht] as %e Hout
    | wp_apply wp_Flock fd (W64 4 ||| W64 1) d (some false) true (by rfl) (fun _ => hfree)
        $$ [Hinv Hfd Ht] as %e Hout
    · iframe; isplitl []; iexact Hinv; iexact Ht
    unfold lockOut
    icases Hout with ⟨%d', Hfd, Ht, %hd⟩
    obtain ⟨-, h2, h3⟩ := hd
    by_cases he : e = 0
    · subst he; have hd' := h2 rfl; subst hd'; unfold errnoErr; rw [if_pos rfl]
      wp_auto
      wp_for_post
      iapply HΦ; iframe; ileft; iframe; ipureintro; rfl
    · have hd' := h3 (by simp) he; subst hd'
      unfold errnoErr; rw [if_neg he]
      wp_auto
      wp_if_destruct <;> (try wp_auto) <;>
        first
        | (wp_for_post; iapply HΦ; iframe; iright; iframe; ipureintro; intro h; cases h; done)
        | (wp_apply wp_Sleep; wp_for_post; iframe))

end proof

end osfs_bboltfs
end EtcdGrove
end Perennial
