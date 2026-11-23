/-
Lean-first (no Rocq counterpart). #33 S3b W7 (2026-11-23): the proof of `Checker.End` (`check.go`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Checker__End
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0Laws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Checker.End.wp_proof : Checker.End.spec (GF := GF) (hG := hG) := by
  intro p c
  wp_start as ⟨Hc, %Hb⟩
  iunfold checkerOwn at Hc
  icases Hc with ⟨%g, Hp, #Hs, #Hv, %Hd⟩
  obtain ⟨gs, gd, gv⟩ := g
  simp only at Hd
  subst Hd
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hpn⟩
  iStructNamed Hp
  wp_auto
  cases hd : c.done
  · obtain ⟨b, E, hb, hW⟩ := Hb hd
    have hi1 := hW.2.1
    have hi2 := hW.2.2.1
    unfold numBound at hb
    ihave #Hs' := Hs
    iunfold stateRO at Hs'
    iNamed Hs'
    iNamed Hf
    iStructNamedSuffix Hp "s"
    wp_pures
    wp_auto
    iapply HΦ
    unfold Checker.finish; simp only [hd, Bool.false_eq_true, ↓reduceIte]
    isplitr
    · iunfold verdictRO
      isplitr
      · ipureintro
        refine ⟨rfl, ?_, rfl⟩
        rw [sint_sub_one (by omega), HI]
      · iapply Init0_strsNil
    iunfold checkerOwn
    iexists { State' := gs, Done' := c.done, Verdict' := gv }
    simp only [hd]
    isplitl [State Done Verdict]
    · iapply typedPointsto_combine _ _ _ Hpn
      simp only [TypedPointsto.typedPointstoDef, named]
      iframe
    iframe Hs Hv
  · wp_pures
    wp_auto
    iapply HΦ
    unfold Checker.finish; simp only [hd, ↓reduceIte]
    isplitr
    · iexact Hv
    iunfold checkerOwn
    iexists { State' := gs, Done' := c.done, Verdict' := gv }
    simp only [hd]
    isplitl [State Done Verdict]
    · iapply typedPointsto_combine _ _ _ Hpn
      simp only [TypedPointsto.typedPointstoDef, named]
      iframe
    iframe Hs Hv

end proof

end AntCheck
end EtcdGrove
end Perennial
