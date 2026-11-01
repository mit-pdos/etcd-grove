/- Lean-first (no Rocq counterpart). The proof of `db.munmap()`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__munmap
public import Spec.golang_org.x.sys.unix.Munmap

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

theorem DB.munmap.wp_proof (wp_Munmap : golang_org.x.sys.unix.Munmap.spec (GF := GF) (hG := hG)) :
    DB.munmap.spec (GF := GF) (hG := hG) := by
  intro db sl dsz m0 m1 p m
  wp_start as ⟨Hd, Hs, H0, H1, Hm⟩
  unfold mappingRes
  icases Hm with (%Hnil | ⟨%base, %len, %vf, %Hsl, #Hinv, Hm, Hc⟩)
  · subst Hnil
    wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    iframe
    unfold unmappedRes
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  · obtain ⟨rfl, Hpos, Hlen, Hb⟩ := Hsl
    have hne : ({ ptr := base, len := len, cap := len } : GoSlice) ≠ slice.nil := by
      intro h; have := congrArg GoSlice.ptr h; simp [slice.nil] at this; subst this
      simp [null] at Hpos
    wp_auto
    rw [decide_eq_false hne]
    wp_auto
    wp_apply wp_Munmap base len p m vf Hlen Hb $$ [Hinv Hm Hc] as %e He
    · iframe; iframe #
    (try wp_auto)
    iapply HΦ
    simp only [hne, ↓reduceIte]
    iframe
    unfold unmappedRes
    iright
    iexists base, len, vf, e
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
