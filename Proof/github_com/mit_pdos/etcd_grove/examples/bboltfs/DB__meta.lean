/- Lean-first (no Rocq counterpart). The proof of `db.meta()`: `pickMeta`, which is not nil when a meta is valid. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__meta
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.pickMeta

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

theorem pickMetaRes_ne_null [GooseExts] (m0 m1 : Loc) (v0 v1 : Meta) (h0 : m0 ≠ null)
    (h1 : m1 ≠ null) (hv : metaValid v0 ∨ metaValid v1) : pickMetaRes m0 v0 m1 v1 ≠ null := by
  unfold pickMetaRes pickValid
  split <;> rcases hv with hv | hv <;> by_cases h0v : metaValid v0 <;>
    by_cases h1v : metaValid v1 <;> simp only [h0v, h1v, ↓reduceIte] <;> first | assumption | exact absurd hv ‹_›

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

theorem DB.«meta».wp_proof (wp_pickMeta : pickMeta.spec (GF := GF) (hG := hG)) :
    DB.«meta».spec (GF := GF) (hG := hG) := by
  intro db m0 m1 v0 v1 dq dq0 dq1 hv
  wp_start as ⟨F0, F1, H0, H1, %Hpos⟩
  have hn0 : m0 ≠ null := by intro h; subst h; simp [null] at Hpos
  have hn1 : m1 ≠ null := by intro h; subst h; simp [null] at Hpos
  have hne := pickMetaRes_ne_null m0 m1 v0 v1 hn0 hn1 hv
  wp_auto
  wp_apply wp_pickMeta m0 m1 v0 v1 dq0 dq1 $$ [H0 H1] as ⟨H0, H1⟩
  · iframe; ipureintro; exact Hpos
  wp_if_destruct
  · exact absurd Hif hne
  · (try wp_auto)
    iapply HΦ
    iframe
