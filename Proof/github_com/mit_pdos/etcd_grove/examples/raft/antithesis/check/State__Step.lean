/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the proof of `State.Step` (B 766-772).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Step
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Bind
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__idx
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Parts

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

theorem State.Step.wp_proof
    (wp_idx : State.idx.spec (GF := GF) (hG := hG))
    (wp_Bind : State.Bind.spec (GF := GF) (hG := hG)) :
    State.Step.spec (GF := GF) (hG := hG) := by
  intro p s e ev o
  wp_start as ⟨#Hs, #He, %HBd, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  ihave #He' := He
  iunfold eventRO at He'
  icases He' with ⟨%ge, #Hge, %Hgf, -⟩
  iStructNamed Hge
  have HBd' := HBd
  obtain ⟨bb, EE, HW, -, -, hbb, -⟩ := HBd'
  have hib : s.i < 2 ^ 61 := by
    have := HW.i_le; unfold numBound Event.weight at hbb; push_cast at hbb; omega
  unfold State.step at Ho
  split at Ho
  · cases Ho
  rename_i hbad
  have hbad' : ev.bad = [] := by simpa using hbad
  obtain ⟨k, hk, Ho⟩ := bind_ok Ho
  obtain ⟨o', hob, Ho⟩ := bind_ok Ho
  wp_auto
  rw [Hgf.2.2.1, decide_eq_true hbad']
  try wp_auto
  rw [Hgf.2.1]
  wp_apply wp_idx p s ev.node k $$ [Hs] as %w %Hw
  · iframe Hs; ipureintro; exact hk
  try wp_auto
  have hwn : sint.nat w = k := by have := sint_nat_cast (k := w) (by omega); omega
  wp_apply wp_Bind p s w e ev o' $$ [Hs He] as %q %ok Hsucc
  · iframe Hs He; ipureintro; exact ⟨by omega, by omega, HBd, by rw [hwn]; exact hob⟩
  try wp_auto
  cases o' with
  | none =>
    simp only [pure_ok, Except.ok.injEq] at Ho
    subst Ho
    iunfold succOwn at Hsucc
    icases Hsucc with %Hok
    subst Hok
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  | some ns =>
  simp only [pure_ok, Except.ok.injEq] at Ho
  subst Ho
  iunfold succOwn at Hsucc
  icases Hsucc with ⟨%Hok, Hns⟩
  subst Hok
  try wp_auto
  wp_apply wp_set_i q ns (g.I' + W64 1) $$ [Hns] as Hns
  · iexact Hns
  try wp_auto
  have hI : sint.Z (g.I' + W64 1) = s.i + 1 := by
    rw [sint_add (by rw [HI, sint_one]; have := HW.i_pos; omega) (by rw [HI, sint_one]; omega), HI, sint_one]
  rw [hI]
  iapply HΦ
  iunfold succOwn
  isplitr
  · ipureintro; rfl
  iexact Hns

end proof

end AntCheck
end EtcdGrove
end Perennial
