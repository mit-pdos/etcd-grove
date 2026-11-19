/- Lean-first (no Rocq counterpart). The proof of `db.munmap()`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__munmap
public import Spec.golang_org.x.sys.unix.Munmap

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

theorem DB.munmap.wp_proof (wp_Munmap : golang_org.x.sys.unix.Munmap.spec (GF := GF) (hG := hG)) :
    DB.munmap.spec (GF := GF) (hG := hG) := by
  intro db dq sl dsz m0 m1 p m Hdq
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
    obtain rfl := Hdq hne
    wp_auto
    rw [decide_eq_false hne]
    wp_auto
    wp_apply wp_Munmap base len p m vf Hlen Hb $$ [Hinv Hm Hc] as %e He
    · iframe; iframe #
    (try wp_auto)
    ihave He : (⌜e = 0⌝ ∗ osMeta p (DFrac.own 1) { m with maps := GMap.delete base m.maps }) ∨
        (⌜e ≠ 0⌝ ∗ (osMeta p (DFrac.own 1) { m with maps := GMap.delete base m.maps } ∨
          (osMeta p (DFrac.own 1) m ∗ cellsR base 0 len.toNat vf))) $$ [He]
    · icases He with (He | ⟨%he, He⟩)
      · ileft; iexact He
      · iright; iframe He; ipureintro; exact he.1
    iapply HΦ
    simp only [hne, ↓reduceIte]
    iframe
    unfold unmappedRes
    iright
    iexists base, len, vf, e
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
