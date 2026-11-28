/-
`hraftnet.raftConfig`'s proof: `DefaultConfig` with the kit's options, which `cfgOk` accepts.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.raftConfig
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rnd
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.serverID
public import Dsverify.Spec.github_com.hashicorp.raft.DefaultConfig
@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet

open github_com.hashicorp.raft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

set_option goose.wp.extras true

theorem raftConfig.wp_proof (wp_DefaultConfig : github_com.hashicorp.raft.DefaultConfig.spec (GF := GF))
    (wp_rnd : rnd.spec (GF := GF)) (wp_serverID : serverID.spec (GF := GF)) :
    raftConfig.spec (GF := GF) := by
  intro id
  wp_start as -
  ihave #Hr : isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_DefaultConfig as %cp Hcp
  wp_apply wp_serverID
  wp_apply (wp_rnd (W64 16) (by decide)) as %m1 %Hm1
  wp_apply (wp_slice_literal (V := w64) [W64 1, W64 4, W64 32])
  isplitr
  · ipureintro; rfl
  iintro %tsl ⟨Htsl, -⟩
  wp_apply (wp_rnd (W64 3) (by decide)) as %m2 %Hm2
  simp only [go.arrayLiteralSize, List.foldl_cons, List.foldl_nil, Int.reduceAdd]
  simp only [show (Max.max (Max.max (3 : Int) 0) 0) = 3 from rfl]
  have hm2 : 0 ≤ sint.Z m2 ∧ sint.Z m2 < sint.Z (W64 3) := by constructor <;> word
  rw [if_pos hm2.2]
  obtain ⟨tl, htl⟩ : ∃ tl : w64, [W64 1, W64 4, W64 32][(sint.Z m2).toNat]? = some tl :=
    ⟨_, List.getElem?_eq_getElem (by simp; word)⟩
  wp_apply (wp_load_slice_index _ (sint.Z m2) _ (DFrac.own 1) tl hm2.1) $$ [$Htsl] as -
  · ipureintro; exact htl
  have hne : sidOf id ≠ [] := sidOf_ne_nil id
  wp_apply (wp_rnd (W64 2) (by decide)) as %m3 %Hm3
  wp_if_destruct
  · wp_auto
    iapply HΦ
    iexists _
    iframe
    ipureintro
    unfold cfgOk
    simp only [defaultConfig]
    (repeat' apply And.intro) <;> first | rfl | exact hne | word
  · wp_auto
    iapply HΦ
    iexists _
    iframe
    ipureintro
    unfold cfgOk
    simp only [defaultConfig]
    (repeat' apply And.intro) <;> first | rfl | exact hne | word

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
